-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_L1mesh_signed_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:16:52.530015+00:00
-- url     : https://prove2.me/submissions/a906d22d-14f3-4660-b938-b9eb4e2ed60c

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The probabilistic L¹-error convergence of a genuine physical stopped
    cash grid is sufficient for all six BV signed Fatou witness clauses. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ) (c : ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hRm : AEStronglyMeasurable R P)
    (hL1 : Tendsto (fun n => eLpNorm (F n - R) 1 P)
      atTop (nhds 0)) :
    ∃ F' M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ c + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (R ω) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by
  have hMeasure : TendstoInMeasure P F atTop R :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      (fun n => (hFm n).aestronglyMeasurable) hRm hL1
  obtain ⟨ns, _hmono, hAE⟩ := hMeasure.exists_seq_tendsto_ae
  have hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (R ω) ≤
        liminf (fun n => ENNReal.ofReal (F (ns n) ω)) atTop := by
    filter_upwards [hAE] with ω hω
    have hENN : Tendsto (fun n => ENNReal.ofReal (F (ns n) ω)) atTop
        (nhds (ENNReal.ofReal (R ω))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hω
    rw [hENN.liminf_eq]
  exact AvramDividend.Classical.avram_limit2_signed_grid_envelope_of_expected_upper
    P c (fun n => F (ns n)) (fun ω => ENNReal.ofReal (R ω))
    (fun n => hFm (ns n)) (fun n => hFi (ns n))
    (fun n => hFn (ns n)) (integrable_const c) (by simp)
    (fun n => hMean (ns n)) hFatou
