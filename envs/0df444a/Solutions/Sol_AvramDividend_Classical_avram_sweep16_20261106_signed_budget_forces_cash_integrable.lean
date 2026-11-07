-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_signed_budget_forces_cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:28:07.554447+00:00
-- url     : https://prove2.me/submissions/257db2e3-13a1-4f9e-8676-654fe1403d8b

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
    (hCashMeas : AEStronglyMeasurable Cash P)
    (hCashNonneg : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hTermI : Integrable Term P)
    (hMI : Integrable M P)
    (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hUpper : ∀ᵐ ω ∂P, Term ω + Cash ω ≤ c + M ω + G ω + H ω) :
    Integrable Cash P := by
  have hc : Integrable (fun _ : Ω => c) P := integrable_const c
  have hEnvelope : Integrable (fun ω => c + M ω + G ω + H ω - Term ω) P := by
    exact (((hc.add hMI).add hGI).add hHI).sub hTermI
  apply hEnvelope.mono' hCashMeas
  filter_upwards [hCashNonneg, hUpper] with ω hnonneg hupper
  have hbound : Cash ω ≤ c + M ω + G ω + H ω - Term ω := by
    linarith
  have henvelope : 0 ≤ c + M ω + G ω + H ω - Term ω :=
    le_trans hnonneg hbound
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg henvelope] using hbound
