-- Prove2me | solution 1 for FamousTheorems.cantor_normal_form_eval_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:57:42.839148+00:00
-- url     : https://prove2.me/submissions/feeb7204-81f9-42e2-b928-34589010913a

import Mathlib

theorem solution (b o : Ordinal) :
    (Ordinal.CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o :=
  Ordinal.CNF.foldr b o
