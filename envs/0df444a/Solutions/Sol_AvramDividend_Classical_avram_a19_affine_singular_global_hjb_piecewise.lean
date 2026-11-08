-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_global_hjb_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:28:08.492072+00:00
-- url     : https://prove2.me/submissions/f1e82eb9-7452-4c8b-9a14-93934c441fc4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_hjb_drift_two_scalar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- The actual characteristic-drift-zero affine HJB deficit is nonpositive at all positive reserves. -/
theorem solution (x : ℝ) (hx : 0 < x) :
    (if x < 1 then
      3 + x - 4 * Real.sqrt x - 2 / Real.sqrt x
    else -(1 + x)) ≤ 0 := by
  by_cases hlt : x < 1
  · simp only [if_pos hlt]
    have hstrong :=
      avram_a19_affine_singular_hjb_drift_two_scalar x hx (le_of_lt hlt)
    linarith
  · simp only [if_neg hlt]
    linarith
