-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn53_origin_integrated_BV_HJB_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:04:15.017871+00:00
-- url     : https://prove2.me/submissions/9a4e7b73-c543-49ce-93b7-2538fe0f35e1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_integrated_original_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_jump_loss_upper

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
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    X.drift * w ε ≤
      (q * ε + (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν)) * w ε := by
  exact (avram_route_bv_drift9_integrated_original_HJB_source X hBV q hq
    w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad hwzero ε hε hεC hε1).trans
    (avram_route_bv_drift9_original_spatial_jump_loss_upper X hBV q hq
      w C hC hw_cont hw0 hw_neg hw_smooth hw_grad hwzero ε hε hεC hε1)
