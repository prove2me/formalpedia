-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_small_jump_absolute_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:44:45.023512+00:00
-- url     : https://prove2.me/submissions/30a31afd-029d-482a-b0e2-3155cc455739

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original positive-cap C1 hypothesis supplies a finite quantitative
BV source-jump compensator absolute drift bound on the unit negative band. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u : ℝ) (ha : 0 < a)
    (hb : ENNReal.ofReal b < C)
    (hu : u ∈ Icc (a + 1) b) :
    ∃ K : ℝ≥0,
      (∫ z in Ioo (-1 : ℝ) 0, |w (u + z) - w u| ∂X.ν) ≤
        (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) := by
  have hsub : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    rcases mem_Icc.mp hy with ⟨hya, hyb⟩
    exact ⟨lt_of_lt_of_le ha hya,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hyb) hb⟩
  have hw' : ContDiffOn ℝ 1 w (Icc a b) := hw.mono hsub
  obtain ⟨K, hLip⟩ := hw'.exists_lipschitzOnWith
    (by norm_num) (convex_Icc a b) isCompact_Icc
  exact ⟨K,
    avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
      X hBV w K a b u hLip hu⟩
