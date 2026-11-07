-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_natural_l1_residual_to_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:15:06.030744+00:00
-- url     : https://prove2.me/submissions/128c2b40-d7b4-4e55-83ce-001f7a8930f9

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_one_sided_hjb_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_closed_budgets_imply_full_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ)
    (hClock : ∀ n : ℕ, 0 < n →
      (∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ (n : ℝ≥0)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : WithTop ℝ≥0)) ∧
      (∀ ω, (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
        ruinTime X x D ω))
    (hResidual : ∀ n : ℕ, 0 < n → ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 ∨
        (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) <
          ruinTime X x D ω then
        x + X.X (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω
        else riskProcess X x D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω =
        Real.exp (-(q * (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ))) *
          w (W ω)) ∧
      Integrable Term P ∧ Integrable Cash P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by
  have hNatural : ∀ n : ℕ, 0 < n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
    intro n hn
    rcases hClock n hn with ⟨hBound, hStop, hRuin⟩
    rcases hResidual n hn with ⟨W, Cash, Term, M, G, H, hW, hCash, hTerm,
      hTermI, hCashI, hMI, hGI, hHI, hMzero, hGH, hUpper⟩
    have hBudget := avram_wave6_06_original_one_sided_hjb_expected_budget
      X q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD
      (fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
      (n : ℝ≥0) hBound hStop hRuin W Cash Term M G H
      hW hCash hTerm hTermI hCashI hMI hGI hHI hMzero hGH hUpper
    exact hBudget.2.2.2
  exact avram_sweep16_20261106_natural_closed_budgets_imply_full_horizon
    X x q T D (ENNReal.ofReal (w x)) hNatural
