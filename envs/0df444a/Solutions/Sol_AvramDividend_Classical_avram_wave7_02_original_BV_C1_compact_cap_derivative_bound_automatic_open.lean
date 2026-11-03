-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:51:03.170974+00:00
-- url     : https://prove2.me/submissions/a9c447b7-d12b-489c-9cc4-caa1cf0aed3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Under the original BV positive-cap C1 assumption and the source openness theorem, the genuine compact reserve strip has a uniformly bounded physical derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc a b, |deriv w y| ≤ K := by
  have hOpen : IsOpen
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  have hCont :
      ContinuousOn (deriv w)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  have hContBand : ContinuousOn (deriv w) (Icc a b) :=
    hCont.mono hBand
  obtain ⟨K, hK⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hContBand
  refine ⟨|K|, abs_nonneg K, ?_⟩
  intro y hy
  have hb : ‖deriv w y‖ ≤ K := hK y hy
  have hb' : |deriv w y| ≤ K := by
    simpa only [Real.norm_eq_abs] using hb
  exact hb'.trans (le_abs_self K)
