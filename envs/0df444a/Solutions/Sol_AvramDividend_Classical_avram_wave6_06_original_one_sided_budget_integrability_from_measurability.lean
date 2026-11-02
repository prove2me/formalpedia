-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_one_sided_budget_integrability_from_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:12:35.224845+00:00
-- url     : https://prove2.me/submissions/79dc6c48-f75c-4b72-8a1d-3c689a0e13f8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- One-sided original stopped budget domination gives terminal and full-cash
integrability as soon as those two observables are strongly measurable a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashMeas : AEStronglyMeasurable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hUpper : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    Integrable Term P ∧ Integrable Cash P := by
  have hTermNN := avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
    X q w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD τ W Term hW hTerm
  have hCashNN : ∀ ω, 0 ≤ Cash ω := by
    intro ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  letI : IsProbabilityMeasure P := X.isProbability
  have hConst : Integrable (fun _ : Ω => w x) P := integrable_const _
  have hRight : Integrable (fun ω => w x + M ω + G ω + H ω) P :=
    ((hConst.add hMI).add hGI).add hHI
  have hTermBound : ∀ᵐ ω ∂P,
      ‖Term ω‖ ≤ ‖w x + M ω + G ω + H ω‖ := by
    filter_upwards [hTermNN, hUpper] with ω htn hup
    have hcn := hCashNN ω
    have hleft : Term ω ≤ w x + M ω + G ω + H ω := by linarith
    have hright : 0 ≤ w x + M ω + G ω + H ω := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg htn,
      abs_of_nonneg hright] using hleft
  have hCashBound : ∀ᵐ ω ∂P,
      ‖Cash ω‖ ≤ ‖w x + M ω + G ω + H ω‖ := by
    filter_upwards [hTermNN, hUpper] with ω htn hup
    have hcn := hCashNN ω
    have hleft : Cash ω ≤ w x + M ω + G ω + H ω := by linarith
    have hright : 0 ≤ w x + M ω + G ω + H ω := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg hcn,
      abs_of_nonneg hright] using hleft
  exact ⟨hRight.mono hTermMeas hTermBound,
    hRight.mono hCashMeas hCashBound⟩
