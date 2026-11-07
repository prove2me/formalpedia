-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_C1_compact_Lipschitz_deriv_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:56:31.955424+00:00
-- url     : https://prove2.me/submissions/98b99182-bba8-40c6-ba4f-699a30e8c5e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_C1_band_deriv_continuous_differentiable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_compact_derivative_uniform_lipschitz_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual dividend value C1 hypotheses supply one compact source
Lipschitz/derivative constant without extra analytic assumptions. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
        |w z - w y| ≤ L * |z - y|) ∧
      (∀ y ∈ Set.Icc a b, |deriv w y| ≤ L) := by
  obtain ⟨hDerCont, hDiff⟩ :=
    avram_bv_error7_original_C1_band_deriv_continuous_differentiable
      w C hwC1 hOpen a b hBand
  exact avram_bv_error7_compact_derivative_uniform_lipschitz_certificate
    w a b hDiff hDerCont
