-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_finite_cap_expected_budget_to_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:26:08.073234+00:00
-- url     : https://prove2.me/submissions/bc1297de-2824-4df2-8902-f9a0bba79d09

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The canonical ENNReal finite-cap source fields admit the exact MGH
    conclusion once their genuine stopped expected budget is established. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCfin : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  have hTI :=
    avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
      X q hq w C hCfin hw_cont hw_neg x hxc D hD
      τ W Term hW hTerm hTermMeas
  exact avram_p4_f_assembly_expected_budget_witness_of_original_L1
    X w x Term Cash hTI hCashI hBudget
