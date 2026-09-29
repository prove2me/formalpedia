-- Prove2me | solution 1 for FamousTheorems.ostrowski_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:27:15.416365+00:00
-- url     : https://prove2.me/submissions/0d4592f5-2273-4368-b696-6ee26aa123c9

import Mathlib

theorem solution (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    f ≈ Rat.AbsoluteValue.real ∨ ∃! p : ℕ, ∃ (_ : Fact p.Prime), f ≈ Rat.AbsoluteValue.padic p :=
  Rat.AbsoluteValue.equiv_real_or_padic f hf
