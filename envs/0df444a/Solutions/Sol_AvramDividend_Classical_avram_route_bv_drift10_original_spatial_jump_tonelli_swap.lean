-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift10_original_spatial_jump_tonelli_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:52:10.757005+00:00
-- url     : https://prove2.me/submissions/e23a0691-7489-4a4d-a66d-ef5f68da5622

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_jump_product_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    (∫ y in Ioc (0 : ℝ) ε,
      (∫ z in Iio (0 : ℝ), w y - w (y + z) ∂X.ν)
      ∂(volume : Measure ℝ)) =
    (∫ z in Iio (0 : ℝ),
      (∫ y in Ioc (0 : ℝ) ε, w y - w (y + z)
        ∂(volume : Measure ℝ)) ∂X.ν) := by
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  exact integral_integral_swap
    (avram_route_bv_drift10_original_spatial_jump_product_L1
      X hBV w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      hwzero ε hε hεC hε1)
