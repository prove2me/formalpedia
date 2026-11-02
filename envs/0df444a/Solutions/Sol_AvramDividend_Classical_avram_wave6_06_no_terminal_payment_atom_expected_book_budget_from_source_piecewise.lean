-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_no_terminal_payment_atom_expected_book_budget_from_source_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:49:37.988532+00:00
-- url     : https://prove2.me/submissions/0d6222f6-1ab4-4c27-844d-02830796cc24

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_no_terminal_right_dividend_piecewise_eq_book
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 < q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hNoAtom : ∀ ω, rightLimit D (τ ω) ω = D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    (∫ ω, Real.exp (-(q * (τ ω : ℝ))) * w (riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω).toReal ∂P) ≤ w x := by
  have hBook : ∀ ω, W ω = riskProcess X x D (τ ω) ω :=
    avram_wave6_06_original_no_terminal_right_dividend_piecewise_eq_book
      X x D τ W hW hNoAtom
  have hEq : (fun ω : Ω =>
      Real.exp (-(q * (τ ω : ℝ))) * w (riskProcess X x D (τ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω).toReal) =
      (fun ω : Ω => Term ω + Cash ω) := by
    funext ω
    rw [hTerm ω, hCash ω, hBook ω]
  rw [hEq]
  exact hBudget
