-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_allcap_ennreal_bound_to_signed_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:35:39.577399+00:00
-- url     : https://prove2.me/submissions/a3be5111-8882-4d22-adc7-a3303ef09491

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_L1_signed_witness_iff_expected_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (hwx : 0 ≤ w x)
    (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hExpected : (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  obtain ⟨hTermI, hBudget⟩ :=
    avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
      w x hwx Term Cash hTermMeas hCashI hTermPos hCashPos hExpected
  exact
    (avram_p4_f_assembly_original_L1_signed_witness_iff_expected_budget
      X w x Term Cash hTermI hCashI).mpr hBudget
