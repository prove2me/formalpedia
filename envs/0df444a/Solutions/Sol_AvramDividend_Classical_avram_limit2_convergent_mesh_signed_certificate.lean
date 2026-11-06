-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_convergent_mesh_signed_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:12:18.9432+00:00
-- url     : https://prove2.me/submissions/7d3f4a2b-b001-4826-9535-4081130a575f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A physical, integrable stopped mesh with its actual upper expectation
    and almost-sure payoff convergence yields all six signed Fatou clauses. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ) (c : ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hConverge : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (nhds (R ω))) :
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
  have hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (R ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop := by
    filter_upwards [hConverge] with ω hω
    have hENN : Tendsto (fun n => ENNReal.ofReal (F n ω)) atTop
        (nhds (ENNReal.ofReal (R ω))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hω
    rw [hENN.liminf_eq]
  exact AvramDividend.Classical.avram_limit2_signed_grid_envelope_of_expected_upper
    P c F (fun ω => ENNReal.ofReal (R ω)) hFm hFi hFn
    (integrable_const c) (by simp) hMean hFatou
