-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_countable_bounded_stopped_piecewise_terminal_real_integrals_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:53:19.857019+00:00
-- url     : https://prove2.me/submissions/b07d2da6-bf92-4a22-b4f9-eba385e26f05

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original Chat 06 real terminal expectations are nonnegative at every
    bounded stochastic localiser; no integrability claim is introduced. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : ℕ → Ω → ℝ≥0) (T : ℕ → ℝ≥0)
    (hτBound : ∀ n ω, τ n ω ≤ T n)
    (hτstop : ∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ n ω : WithTop ℝ≥0)))
    (hτruin : ∀ n ω, (τ n ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Term : ℕ → Ω → ℝ)
    (hW : ∀ n ω, W n ω =
      if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω
      else riskProcess X x D (τ n ω) ω)
    (hTerm : ∀ n ω, Term n ω =
      Real.exp (-(q * (τ n ω : ℝ))) * w (W n ω)) :
    ∀ n : ℕ, 0 ≤ ∫ ω, Term n ω ∂P := by
  intro n
  apply integral_nonneg_of_ae
  exact avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg
    X hBV q w C hw0 hw_cont hw_neg hw_smooth hw_grad
    x hxc D hD (τ n) (W n) (Term n) (hW n) (hTerm n)
end
