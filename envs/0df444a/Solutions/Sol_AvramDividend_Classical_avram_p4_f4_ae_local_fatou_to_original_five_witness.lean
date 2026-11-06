-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_ae_local_fatou_to_original_five_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:10:53.455296+00:00
-- url     : https://prove2.me/submissions/899f3b07-8c0f-413f-b21f-379f28117089

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_five_witness_iff_expected_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A genuine almost-surely convergent local stopped payoff budget yields
five actual natural-clock existential witnesses without martingale UI. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermNonneg : 0 ≤ᵐ[P] Term)
    (hCashNonneg : 0 ≤ᵐ[P] Cash)
    (F : ℕ → Ω → ℝ)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hlim : ∀ᵐ ω ∂P, Tendsto
      (fun k => ENNReal.ofReal (F k ω)) atTop
      (𝓝 (ENNReal.ofReal (Term ω + Cash ω))))
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ b) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  have hSMeas :
      AEStronglyMeasurable (fun ω => Term ω + Cash ω) P :=
    hTermMeas.add hCashI.aestronglyMeasurable
  have hSNonneg : 0 ≤ᵐ[P] (fun ω => Term ω + Cash ω) := by
    filter_upwards [hTermNonneg, hCashNonneg] with ω ht hc
    exact add_nonneg ht hc
  obtain ⟨hSI, hMean⟩ :=
    avram_p4_f4_ae_natural_clock_fatou_L1_budget
      P (fun ω => Term ω + Cash ω) F hSMeas hSNonneg
      hFmeas hFint hFnonneg hlim b hb hBudget
  have hTermI : Integrable Term P := by
    have hFun : (fun ω => Term ω + Cash ω) - Cash = Term := by
      funext ω
      change Term ω + Cash ω - Cash ω = Term ω
      ring
    simpa only [hFun] using (hSI.sub hCashI)
  exact (avram_p4_f4_five_witness_iff_expected_budget
    Term Cash hTermI hCashI b).mp hMean
