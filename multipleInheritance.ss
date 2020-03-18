(require mzlib/defmacro)
(require scheme/mpair)
(require scheme/list)

(define (merge seqs)
  (define result (mlist))
  (define (loop seqs)
    (let ((nonemptySeqs (filterEmpty seqs)))
      (if (not (empty? nonemptySeqs))
          (let ((cand (findCandidate nonemptySeqs)))
            (if (not cand)
                (error "inconsistent hierarchy")
                (begin (set! result (mcons cand result))
                       (loop (removeCandidate cand nonemptySeqs))))))))
  (define (filterEmpty seqs)
    (define result (mlist))
    (define (loop seqs)
      (if (not (empty? seqs))
          (let ((head (mcar seqs))
                (tail (mcdr seqs)))
            (if (not (empty? head))
                (set! result (mcons head result)))
            (loop tail))))
    (loop seqs)
    (mreverse result))
  (define (findCandidate origseqs)
    (define result false)
    (define (loop seqs)
      (if (not (empty? seqs))
          (let ((head (mcar (mcar seqs))))
            (if (elementOfTails head origseqs)
                (loop (mcdr seqs));not a good head
                (set! result head))))) ;good head
    (define (elementOfTails element seqs)
      (if (empty? seqs)
          false
          (if (mmember element (mcdr (mcar seqs)))
              true
              (elementOfTails element (mcdr seqs)))))
    (loop origseqs)
    result)
  (define (removeCandidate cand seqs)
    (define result (mlist))
    (define (loop seqs)
      (if (not (empty? seqs))
          (begin
            (if (eq? (mcar (mcar seqs)) cand)
                (set! result (mcons (mcdr(mcar seqs)) result))
                (set! result (mcons (mcar seqs) result)))
            (loop (mcdr seqs)))))
    (loop seqs)
    (mreverse result))
  (loop seqs)
  (mreverse result))

(define (<<TABLE>>)
  (define tab '())
  (lambda (op . rest)
    (case op
      ((instantiate)
       (let ((table (<<TABLE>>)))
         (mfor-each
          (lambda (elt)
            (table 'put (mcar elt) (eval (mcdr elt))))
          tab)
         table))
      ((copy)
       (let ((table (<<TABLE>>)))
         (mfor-each
          (lambda (elt)
            (table 'put (mcar elt) (mcdr elt)))
          tab)
         table))
      ((get)
       (let* ((key (car rest))
              (entry (massoc key tab)))
         (if entry
             (mcdr entry)
             #f)))
      ((put)
       (let* ((key (car rest))
              (entry (massoc key tab))
              (value (cadr rest)))
         (if entry
             (error "duplicate name" key)
             (set! tab (mcons (mcons key value) tab)))))
      ((replace)
       (let* ((key (car rest))
              (entry (massoc key tab))
              (value (cadr rest)))
         (if entry
             (set-mcdr! entry value)
             (error "undefined name" key))
         #t))
      ((<<CONTENT>>)
       tab)
      )))

(define Root
  (lambda (msg . args)
    (case msg
      ((new)
       (error "cannot instantiate root class"))
      ((<<EVAL>>)
       (let*
           ((msg (cadr args)))
         (error "method not found " msg)))
      ((<<SINGLETONEVAL>>)
       (let*
           ((msg (cadr args)))
         (error "method not found " msg)))
      ((<<COPY>>)
       (let ((tab (<<TABLE>>)))
         (tab 'put '<<SELF>> '())
         tab))
      ((<<GETSUPERS>>) (mlist))
      (else
       (error "invalid class message " msg)))))


(define-macro VAR
  (lambda (name value)
    `(if (<<VARS>> 'get ',name)
         (<<VARS>> 'replace ',name ',value)
         (<<VARS>> 'put ',name ',value))))

(define-macro METHOD
  (lambda (msg args . body)
    `(<<METHODS>> 'put ',msg (lambda (<<CONTEXT>> ,@args) ,@body))))

(define-macro ?
  (lambda (name)
    `(<<CONTEXT>> 'get ',name)))

(define-macro !
  (lambda (name value)
    `(<<CONTEXT>> 'replace ',name ,value)))

(define-macro NEW
  (lambda (class)
    `(,class 'new)))

(define-macro SEND
  (lambda (object msg . args)
    `(,object ',msg ,@args)))

(define-macro SELF
  (lambda ()
    `(<<CONTEXT>> 'get '<<SELF>>)))

(define-macro SUPER
  (lambda (msg . args)
    `(<<SUPER>> '<<EVAL>> <<CONTEXT>> ',msg ,args)))

(define (mergeTables tableList)
  (let ((result (<<TABLE>>)))
    (define (loop tableList)
      (if (not (empty? tableList))
          (begin (insertAll (mcar tableList))
                 (loop (mcdr tableList)))))
    (define (insertAll table)
      (mmap (λ(entry)
              (let* ((key (mcar entry))
                     (value (mcdr entry))
                     (present (result 'get key)))
                (if present
                    'skip
                    (result 'put key value))))
            (table '<<CONTENT>>)))
    (loop tableList)
    result))

(define (evalWithFirstSuper superList context msg args)
  (if (empty? superList)
      (error "method not found") ;this should not happen, because it is captured by the Root class
      (let ((result ((mcar superList) '<<SINGLETONEVAL>> context msg args)))
        (if (equal? result '<<METHODNOTFOUND>>)
            (evalWithFirstSuper (mcdr superList) context msg args)
            result))))

(define (flattenSuperList lst)
  (define result (mlist))
  (define (loop lst)
    (if (not (empty? lst))
        (begin (set! result (mappend result (mlist (mcons (mcar lst) ((mcar lst) '<<GETSUPERS>>)))))
               (loop (mcdr lst)))))
  (loop lst)
  (merge (mappend result (mlist lst))))

(define-macro MYCLASS
  (lambda (superlist . defs)
    `(letrec
         ((<<SUPERS>> (flattenSuperList ,superlist))
          (<<METHODS>> (<<TABLE>>))
          (<<VARS>> (mergeTables (mmap (λ(super)(super '<<COPY>>))<<SUPERS>>)))
          (<<CLASS>>
           (lambda (msg . args)
             (case msg
               ((new)
                (let*
                    ((context (<<VARS>> 'instantiate))
                     (self 
                      (lambda (msg . args)
                        (<<CLASS>> '<<EVAL>> context msg args))))
                  (context 'replace '<<SELF>> self)
                  self))
               ((<<EVAL>>)
                (let*
                    ((context (car args))
                     (msg (cadr args))
                     (args (caddr args))
                     (entry (<<METHODS>> 'get msg)))
                  (if entry
                      (apply entry (cons context args))
                      (evalWithFirstSuper <<SUPERS>> context msg args)
                      )))
               ((<<SINGLETONEVAL>>)
                (let*
                    ((context (car args))
                     (msg (cadr args))
                     (args (caddr args))
                     (entry (<<METHODS>> 'get msg)))
                  (if entry
                      (apply entry (cons context args))
                      '<<METHODNOTFOUND>>
                      )))
               ((<<COPY>>)(<<VARS>> 'copy))
               ((<<GETVARS>>) <<VARS>>)
               ((<<GETSUPERS>>) <<SUPERS>>)
               (else
                (error "invalid class message " msg))))))
       ,@defs
       <<CLASS>>)))


(define X (MYCLASS (mlist Root)
                   (VAR lol 10)
                   (METHOD test () (display 'X))
                   (METHOD get () (? lol))))
(define Y (MYCLASS (mlist Root)
                   (VAR lol 11)
                   (METHOD test () (display 'Y))))
(define A (MYCLASS (mlist X Y Root)
                   (VAR lol 12)
                   ;(METHOD test () (display 'A))
                   ))
(define B (MYCLASS (mlist Y X Root)
                   (VAR lol 13)
                   ;(METHOD test () (display 'B))
                   ))
;(define C (MYCLASS (mlist A B)))
(define x (C 'new))
(SEND x get)
(SEND x test)
