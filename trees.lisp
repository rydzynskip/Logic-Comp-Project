; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(defdata tree (oneof rational (list rational tree tree))) 
(defdata lor (listof rational))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
    b
    (cons (first a) (app2 (rest a) b))))
 
(definec tree-max (tr :tree) :rational
  (if (rationalp tr)
    tr
    (max (car tr)
         (max (tree-max (cadr tr))
              (tree-max (caddr tr))))))

(definec tree-min (tr :tree) :rational
  (if (rationalp tr)
    tr
    (min (car tr) 
         (min (tree-min (cadr tr))
              (tree-min (caddr tr))))))

(definec ordered-treep (tr :tree) :bool
  (cond
   ((rationalp tr) t)
   ((consp tr) (and (ordered-treep (cadr tr))
                    (ordered-treep (caddr tr))
                    (<= (tree-max (cadr tr)) (car tr))
                    (>= (tree-min (caddr tr)) (car tr))))))

(definec inorder-walk (tr :tree) :lor
  (if (rationalp tr) 
    (list tr)
    (app2 (inorder-walk (cadr tr)) 
          (cons (car tr) (inorder-walk (caddr tr))))))

(definec sorted-lorp (ls :lor) :bool
  (cond 
   ((endp ls) t)
   ((endp (cdr ls)) t)
   (t (and (<= (car ls) (cadr ls))
           (sorted-lorp (cdr ls))))))


;; =======================================================
;; LEMMAS DEALING WITH MINIMUM AND FIRST ELEMENTS
;; =======================================================

;; the minimum of a tree is equal to the minimum of the left sub tree
(skip-proofs
 (defthm equal-minimums
   (implies (and (treep tr)
                 (consp tr)
                 (ordered-treep tr))
            (equal (tree-min (cadr tr))
                   (tree-min tr)))))

;; the first element of the inorder walk of a tree is equal to the first element
;; of the in order walk of the left subtree
(skip-proofs
 (defthm equal-first-elements
   (implies (and (treep tr)
                 (consp tr)
                 (ordered-treep tr))
            (equal (car (inorder-walk (cadr tr)))
                   (car (inorder-walk tr))))))

;; the minimum of a tree is the first element in an inorder walk
(defthm inorder-walk-starts-with-min
  (implies (and (treep tr)
                (ordered-treep tr))
           (equal (car (inorder-walk tr))
                  (tree-min tr)))
  :hints (("Goal" :induct (treep tr))))



;; =======================================================
;; LEMMAS DEALING WITH MAXIMUM AND LAST ELEMENTS
;; =======================================================

;; the maximum of a tree is equal to the maximum of the right sub tree
(skip-proofs
 (defthm equal-maximums
   (implies (and (treep tr)
                 (consp tr)
                 (ordered-treep tr))
            (equal (tree-max (caddr tr))
                   (tree-max tr)))))

;; the last element of the inorder walk of a tree is equal to the last element
;; of the in order walk of the right subtree
(skip-proofs
 (defthm equal-last-elements
   (implies (and (treep tr)
                 (consp tr)
                 (ordered-treep tr))
            (equal (car (last (inorder-walk (caddr tr))))
                   (car (last (inorder-walk tr)))))))

;; the miximum of a tree is the last element in an inorder walk
(defthm inorder-walk-ends-with-max
  (implies (and (treep tr)
                (ordered-treep tr))
           (equal (car (last (inorder-walk tr)))
                  (tree-max tr)))
  :hints (("Goal" :induct (treep tr))))



;; =======================================================
;; LEMMAS DEALING WITH APPENDING SORTED LISTS
;; =======================================================

;; appending two sorted lists for which the last of the first is less than
;; the first of the second produces a sorted list
(skip-proofs
 (defthm app2-sorted
   (implies (and (lorp l1)
                 (lorp l2)
                 (consp l1)
                 (consp l2)
                 (sorted-lorp l1)
                 (sorted-lorp l2)
                 (<= (car (last l1)) (car l2)))
            (sorted-lorp (app2 l1 l2)))))




;; main theorem we want to prove
(defthm sorted-inorder-walk 
  (implies (and (treep tr) (ordered-treep tr))
           (sorted-lorp (inorder-walk tr)))
  :hints (("Goal" :induct (treep tr))))#|ACL2s-ToDo-Line|#

                  
                  
      

