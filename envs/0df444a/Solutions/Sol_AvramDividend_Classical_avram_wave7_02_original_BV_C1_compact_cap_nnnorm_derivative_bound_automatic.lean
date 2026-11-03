-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:17:02.091837+00:00
-- url     : https://prove2.me/submissions/746bae61-6397-455b-b0ef-a27cba6bf313

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Uniform original physical C1 derivative norm bound as a nonnegative real. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ≥0, ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K := by
  obtain ⟨M, hMnonneg, hM⟩ :=
    avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
      X hBV C w hwC1 a b hab hBand
  refine ⟨⟨M, hMnonneg⟩, ?_⟩
  intro y hy
  apply NNReal.coe_le_coe.mp
  change (‖deriv w y‖₊ : ℝ) ≤ M
  simpa only [coe_nnnorm, Real.norm_eq_abs] using hM y hy
