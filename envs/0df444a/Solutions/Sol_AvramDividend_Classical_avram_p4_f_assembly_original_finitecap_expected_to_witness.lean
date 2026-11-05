-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finitecap_expected_to_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:53:01.550291+00:00
-- url     : https://prove2.me/submissions/3db1dca7-d0d6-4ff0-b58b-498028fcd4cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q c : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (C : ℝ≥0∞) (hC : C = ENNReal.ofReal c)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (Cash Term : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hExpected : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + M ω + G ω + H ω) := by
  subst C
  have hTermFn :
      Term = (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :=
    funext hTerm
  have hTermMeasFn := hTermMeas
  rw [hTermFn] at hTermMeasFn
  have hTermI : Integrable Term P := by
    rw [hTermFn]
    exact avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound
      X x c hc hxc D hD q (le_of_lt hq)
      τ W hW w hwCont hwNeg hTermMeasFn
  exact avram_p4_f_assembly_expected_budget_witness_of_original_L1
    X w x Term Cash hTermI hCashI hExpected
