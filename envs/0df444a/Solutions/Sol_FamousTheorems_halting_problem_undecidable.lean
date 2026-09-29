-- Prove2me | solution 1 for FamousTheorems.halting_problem_undecidable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:59:43.359565+00:00
-- url     : https://prove2.me/submissions/588f08ad-a204-4b48-ae54-01b34fb169ac

import Mathlib

theorem solution (n : ℕ) : ¬ComputablePred fun c : Nat.Partrec.Code => (c.eval n).Dom :=
  ComputablePred.halting_problem n
