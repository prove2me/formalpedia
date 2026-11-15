-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb26_standing_original_BV_HJB_strict_positive_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:55:40.882491+00:00
-- url     : https://prove2.me/submissions/8fc18881-7ae9-45f1-b6da-d79fbf1eba77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    : 0 < w 0  := by
  have hDrift : 0 < X.drift :=
    (bv_standing_drift_pos X hStanding hBV).1
  exact avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
    X hBV q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hw_gen hw_grad hDrift
