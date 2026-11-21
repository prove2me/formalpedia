-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:03:44.910064+00:00
-- url     : https://prove2.me/submissions/59564cdf-23df-491a-92d0-f0c0bb88f796

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    V (y + z) - V y - deriv V y * z ≤ max 0 (-(y + z)) := by
  dsimp only
  by_cases hz : 0 ≤ y + z
  · have h :=
      avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
        C hC hFinite w hw_cont hw_smooth hw_grad y z hy hz
    have heq : max 0 (-(y + z)) = 0 := max_eq_left (neg_nonpos.mpr hz)
    rw [heq]
    exact h
  · have hzneg : y + z < 0 := lt_of_not_ge hz
    have h :=
      avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
        C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hzneg
    have heq : max 0 (-(y + z)) = -(y + z) :=
      max_eq_right (neg_nonneg.mpr (le_of_lt hzneg))
    rw [heq]
    exact h
