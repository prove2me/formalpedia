-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_hjb_drift_two_scalar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:46:07.297194+00:00
-- url     : https://prove2.me/submissions/2b72afca-ef40-4a19-bd89-e1b2ee20ff61

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- The affine zero-extension HJB expression for physical drift two is nonpositive below reserve one. -/
theorem solution (x : ℝ) (hx : 0 < x) (hcap : x ≤ 1) :
    5 + x - 4 * Real.sqrt x - 2 / Real.sqrt x ≤ 0 := by
  have ht : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hsqmul : (Real.sqrt x) ^ 2 * Real.sqrt x = x * Real.sqrt x :=
    congrArg (fun y : ℝ => y * Real.sqrt x) hsq
  have hle : Real.sqrt x ≤ 1 := by nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hfactor : (Real.sqrt x - 1) ^ 2 * (Real.sqrt x - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  have hmul :
      (5 + x - 4 * Real.sqrt x - 2 / Real.sqrt x) * Real.sqrt x ≤ 0 := by
    have hident :
        (5 + x - 4 * Real.sqrt x - 2 / Real.sqrt x) * Real.sqrt x =
          (Real.sqrt x - 1) ^ 2 * (Real.sqrt x - 2) := by
      field_simp [ne_of_gt ht]
      nlinarith [hsq, hsqmul]
    rw [hident]
    exact hfactor
  by_contra hn
  have hp : 0 < 5 + x - 4 * Real.sqrt x - 2 / Real.sqrt x := lt_of_not_ge hn
  exact (not_lt_of_ge hmul) (mul_pos hp ht)
