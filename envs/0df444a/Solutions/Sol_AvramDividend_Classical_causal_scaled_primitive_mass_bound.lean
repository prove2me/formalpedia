-- Prove2me | solution 1 for AvramDividend.Classical.causal_scaled_primitive_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:56:05.082647+00:00
-- url     : https://prove2.me/submissions/b8e08d5c-3b51-488d-91be-470677bf49e9

import Mathlib

open MeasureTheory Set

theorem solution
    (P F : ℝ → ℝ) (a w x M : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hx : 0 < x)
    (hPL1 : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hFL1 : IntegrableOn F (Ioi (0 : ℝ)) volume)
    (hdom : ∀ s : ℝ, 0 ≤ s → |P s| ≤ F s)
    (hMass : ∫ s in Ioc (0 : ℝ) x, F s ∂volume ≤ M) :
    |(Real.exp (-w * x) *
      (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume)) / a|
      ≤ M / a := by
  have hFI : IntegrableOn F (Ioc 0 x) volume := hFL1.mono_set Ioc_subset_Ioi_self
  have hI : ‖∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume‖ ≤
      ∫ s in Ioc (0 : ℝ) x, Real.exp (w * x) * F s ∂volume := by
    refine norm_integral_le_of_norm_le (hFI.const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hw))
      (hdom s hs.1.le) (abs_nonneg _) (Real.exp_pos _).le
  rw [integral_const_mul] at hI
  rw [abs_div, abs_of_pos ha, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine div_le_div_of_nonneg_right ?_ ha.le
  rw [Real.norm_eq_abs] at hI
  calc Real.exp (-w * x) * |∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume|
      ≤ Real.exp (-w * x) * (Real.exp (w * x) * ∫ s in Ioc (0 : ℝ) x, F s ∂volume) :=
        mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le
    _ = ∫ s in Ioc (0 : ℝ) x, F s ∂volume := by
        rw [← mul_assoc, ← Real.exp_add, show -w * x + w * x = 0 by ring, Real.exp_zero, one_mul]
    _ ≤ M := hMass
