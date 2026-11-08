-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift9_original_negative_mark_loss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:15:06.095845+00:00
-- url     : https://prove2.me/submissions/6cc872cf-da2c-4a47-9a94-b772553a3a81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C)
    (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) ε) (z : ℝ) (hz : z < 0) :
    0 ≤ w y - w (y + z) := by
  have hmon : MonotoneOn w (Icc (0 : ℝ) ε) := by
    intro a ha b hb hab
    have hbc : ENNReal.ofReal b ≤ C := (ENNReal.ofReal_mono hb.2).trans hεC.le
    have hsec := avram_wave3_03_bv_full_cap_gradient_secant C hC w hw_cont
      hw_smooth hw_grad a b ha.1 hab hbc
    linarith
  have hyic : y ∈ Icc (0 : ℝ) ε := ⟨hy.1.le, hy.2⟩
  by_cases hlt : y + z < 0
  · rw [hw_neg (y + z) hlt]
    have hbase := hmon ⟨le_refl (0 : ℝ), hε.le⟩ hyic hy.1.le
    linarith
  · have hnonneg : 0 ≤ y + z := le_of_not_gt hlt
    have hle : y + z ≤ y := by linarith
    have hshift := hmon ⟨hnonneg, hle.trans hy.2⟩ hyic hle
    linarith
