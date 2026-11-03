-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_derivative_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:45:17.234182+00:00
-- url     : https://prove2.me/submissions/a629c50a-2600-4252-982c-5a57d0c6483e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A source-faithful compact-band C¹ bound, using the absolute compact-image witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc a b, |deriv w y| ≤ K := by
  have hOn :
      ContinuousOn (deriv w)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  obtain ⟨M, hM⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hOn.mono hBand)
  refine ⟨|M|, abs_nonneg M, ?_⟩
  intro y hy
  have hNorm : ‖deriv w y‖ ≤ M := hM y hy
  simpa only [Real.norm_eq_abs] using hNorm.trans (le_abs_self M)
