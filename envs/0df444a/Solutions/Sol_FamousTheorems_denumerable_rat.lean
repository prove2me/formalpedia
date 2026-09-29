-- Prove2me | solution 1 for FamousTheorems.denumerable_rat
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:17:24.699313+00:00
-- url     : https://prove2.me/submissions/c4763a27-24f4-41df-8f1f-00431d8ce501

import Mathlib

theorem solution : Nonempty (ℕ ≃ ℚ) :=
  ⟨(Denumerable.eqv ℚ).symm⟩
