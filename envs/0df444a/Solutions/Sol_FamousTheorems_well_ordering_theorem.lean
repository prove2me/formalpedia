-- Prove2me | solution 1 for FamousTheorems.well_ordering_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:09:24.738378+00:00
-- url     : https://prove2.me/submissions/959f5046-90d4-46b2-9d01-501847b637d4

import Mathlib

theorem solution (α : Type*) : ∃ (_ : LinearOrder α), WellFoundedLT α :=
  exists_wellFoundedLT α
