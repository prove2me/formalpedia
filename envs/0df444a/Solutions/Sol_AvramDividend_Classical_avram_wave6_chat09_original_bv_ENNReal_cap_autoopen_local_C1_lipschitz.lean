-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:56:14.670021+00:00
-- url     : https://prove2.me/submissions/1c1f9ce3-f9af-4d26-893d-99ff3e41bbdb

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (l r : ℝ) (hlr : l < r)
    (hBand : Icc l r ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
        |w s - w t| ≤ L * |s - t| := by
  exact avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
    X hBV w C l r hlr
    (avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C)
    hBand hwC1
