-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:06:52.051193+00:00
-- url     : https://prove2.me/submissions/df7501f6-efc6-4114-bb5f-dacea9d348d7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original negative-mark integral is nonpositive even at cap contacts. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ν : Measure ℝ) (b : ℝ) (hb : 0 ≤ b) (hbCap : ENNReal.ofReal b ≤ C) :
    (∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) ≤ 0 := by
  have hwb : 0 ≤ w b := by
    have hs := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad 0 b le_rfl hb hbCap
    linarith
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
  have hzneg : z < 0 := hz
  by_cases hpositive : 0 ≤ b + z
  · have hs := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad (b + z) b hpositive
        (by linarith) hbCap
    dsimp
    linarith
  · have hneg : b + z < 0 := lt_of_not_ge hpositive
    rw [hw_neg _ hneg]
    dsimp
    linarith
