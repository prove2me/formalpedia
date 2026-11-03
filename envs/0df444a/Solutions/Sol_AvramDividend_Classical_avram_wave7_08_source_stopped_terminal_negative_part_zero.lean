-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_stopped_terminal_negative_part_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:52:02.504424+00:00
-- url     : https://prove2.me/submissions/6f76c849-c327-4e60-a560-f18c7ac45ac2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    (∫⁻ ω, ENNReal.ofReal (-Term ω) ∂P) = 0 := by
  have hnonneg :=
    avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
      X hBV q w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD τ W Term hW hTerm
  have hzero : ∀ᵐ ω ∂P, ENNReal.ofReal (-Term ω) = 0 := by
    filter_upwards [hnonneg] with ω ht
    exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr ht)
  calc
    (∫⁻ ω, ENNReal.ofReal (-Term ω) ∂P) =
      (∫⁻ ω, (0 : ℝ≥0∞) ∂P) := lintegral_congr_ae hzero
    _ = 0 := by simp
