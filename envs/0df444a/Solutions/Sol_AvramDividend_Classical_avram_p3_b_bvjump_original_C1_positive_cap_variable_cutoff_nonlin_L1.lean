-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_variable_cutoff_nonlin_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:37:34.197624+00:00
-- url     : https://prove2.me/submissions/d087e441-af56-4464-8dec-a447149819df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_variable_cutoff_nonlin_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original verification value's own C1 condition yields a genuine
finite BV nonlinear small-source-jump integral on each interior band. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b δ u : ℝ) (ha : 0 < a)
    (hb : ENNReal.ofReal b < C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : u ∈ Icc (a + δ) b) :
    IntegrableOn (fun z : ℝ => w (u + z) - w u)
      (Ioo (-δ) 0) X.ν := by
  have hsub : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    rcases mem_Icc.mp hy with ⟨hya, hyb⟩
    exact ⟨lt_of_lt_of_le ha hya,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hyb) hb⟩
  have hw' : ContDiffOn ℝ 1 w (Icc a b) := hw.mono hsub
  obtain ⟨K, hLip⟩ := hw'.exists_lipschitzOnWith
    (by norm_num) (convex_Icc a b) isCompact_Icc
  exact avram_p3_b_bvjump_original_source_BV_variable_cutoff_nonlin_L1
    X hBV w K a b δ u hδ hδ1 hLip hu
