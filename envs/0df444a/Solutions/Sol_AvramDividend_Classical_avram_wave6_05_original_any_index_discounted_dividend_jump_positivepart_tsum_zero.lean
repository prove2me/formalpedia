-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_original_any_index_discounted_dividend_jump_positivepart_tsum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:05:57.240097+00:00
-- url     : https://prove2.me/submissions/82fbd8bd-7f7a-47f4-804c-4acf2b119775

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- The original cap-linear chronological dividend jump cash excess has identically
zero positive part, even for arbitrary infinite index sets of actual payment times.
All simultaneous source and payment jumps are allowed; no summability is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (A : Set ℝ≥0)
    (hA : ∀ t : A,
      (t : ℝ≥0) = 0 ∨
        ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' t : A, ENNReal.ofReal
      (Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          V (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          V (riskProcess X x D (t : ℝ≥0) ω)))) = 0 := by
  have hAtomZero : ∀ t : A,
      ENNReal.ofReal
        (Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            V (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            V (riskProcess X x D (t : ℝ≥0) ω))) = 0 := by
    intro t
    have hDrop :=
      avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
        X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
        D hD ω (t : ℝ≥0) (hA t)
    have hNonpos :
        (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          V (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          V (riskProcess X x D (t : ℝ≥0) ω) ≤ 0 := by
      linarith only [hDrop]
    have hWeighted :
        Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            V (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            V (riskProcess X x D (t : ℝ≥0) ω)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) hNonpos
    exact ENNReal.ofReal_eq_zero.mpr hWeighted
  have hFun :
      (fun t : A => ENNReal.ofReal
        (Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            V (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            V (riskProcess X x D (t : ℝ≥0) ω)))) =
        (fun _ : A => (0 : ℝ≥0∞)) := by
    funext t
    exact hAtomZero t
  rw [hFun]
  exact tsum_zero
