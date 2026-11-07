-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_nonnegative_signed_budget_both_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:28:07.515412+00:00
-- url     : https://prove2.me/submissions/d6c0df36-dfdf-4625-b8f7-896482ca66cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (c : ℝ) (Term Cash M G H : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashMeas : AEStronglyMeasurable Cash P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashNonneg : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hMI : Integrable M P)
    (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hUpper : ∀ᵐ ω ∂P, Term ω + Cash ω ≤ c + M ω + G ω + H ω) :
    Integrable Term P ∧ Integrable Cash P := by
  have hc : Integrable (fun _ : Ω => c) P := integrable_const c
  have hEnvelope : Integrable (fun ω => c + M ω + G ω + H ω) P := by
    exact ((hc.add hMI).add hGI).add hHI
  have hTermI : Integrable Term P := by
    apply hEnvelope.mono' hTermMeas
    filter_upwards [hTermNonneg, hCashNonneg, hUpper] with ω ht hcash hupper
    have hbound : Term ω ≤ c + M ω + G ω + H ω := by linarith
    have henvelope : 0 ≤ c + M ω + G ω + H ω := le_trans ht hbound
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht,
      abs_of_nonneg henvelope] using hbound
  have hCashI : Integrable Cash P := by
    apply hEnvelope.mono' hCashMeas
    filter_upwards [hTermNonneg, hCashNonneg, hUpper] with ω ht hcash hupper
    have hbound : Cash ω ≤ c + M ω + G ω + H ω := by linarith
    have henvelope : 0 ≤ c + M ω + G ω + H ω := le_trans hcash hbound
    simpa only [Real.norm_eq_abs, abs_of_nonneg hcash,
      abs_of_nonneg henvelope] using hbound
  exact ⟨hTermI, hCashI⟩
