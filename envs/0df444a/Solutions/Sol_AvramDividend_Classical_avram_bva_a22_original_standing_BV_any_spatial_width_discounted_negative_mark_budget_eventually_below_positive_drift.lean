-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_standing_BV_any_spatial_width_discounted_negative_mark_budget_eventually_below_positive_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:26:26.32357+00:00
-- url     : https://prove2.me/submissions/1afbf4ec-c99e-42ba-b58d-a9dced07240a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      q * ε n + (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) <
        X.drift := by
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  exact avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
    X hBV hd q ε hε hεlim
