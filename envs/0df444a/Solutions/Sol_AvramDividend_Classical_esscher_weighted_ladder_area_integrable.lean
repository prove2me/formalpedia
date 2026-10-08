-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_ladder_area_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:56:30.517998+00:00
-- url     : https://prove2.me/submissions/2eefe092-b0c8-4c83-8d48-6c46d32bfd0b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_area_integrable
import Theorems.Thm_AvramDividend_Classical_ladder_height_truncated_area_interval_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Set
open scoped ENNReal
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal
      (Real.exp (-(φ * z)) *
        (∫ t in (0 : ℝ)..z, min 1 t)) ∂μ) < ⊤ := by
  have hmem : ∀ᵐ z : ℝ ∂μ.restrict (Ioi (0 : ℝ)), 0 ≤ z := by
    filter_upwards [ae_restrict_mem (μ := μ) measurableSet_Ioi] with z hz
    exact hz.le
  have hpoint : ∀ᵐ z : ℝ ∂μ.restrict (Ioi (0 : ℝ)),
      ENNReal.ofReal
        (Real.exp (-(φ * z)) *
          (∫ t in (0 : ℝ)..z, min 1 t)) ≤
        ENNReal.ofReal (Real.exp (-(φ * z)) * min (z ^ 2) z) := by
    filter_upwards [hmem] with z hz
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (ladder_height_truncated_area_interval_bound z hz)
      (Real.exp_pos _).le
  apply lt_of_le_of_lt ?_
    (esscher_tilted_tail_area_integrable μ φ hφ hlevy)
  exact lintegral_mono_ae hpoint
