-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_rank_marked_cell_l1_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:21:39.844904+00:00
-- url     : https://prove2.me/submissions/fb8632e6-2cfb-4934-aab4-fa8d8d3c8e37

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_product_integrable_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

/-- On one actual marked-Poisson cell, every finite-rank predictable
past-by-mark L¹ integrand has zero centred expectation. -/
theorem solution
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (s : Finset ι)
    (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0)
    (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hHm : ∀ a ∈ s, Measurable (H a))
    (hHi : ∀ a ∈ s, Integrable (H a) μ)
    (hPast : ∀ a ∈ s,
      IndepFun (H a) (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hfm : ∀ a ∈ s, Measurable (f a))
    (hfI : ∀ a ∈ s, Integrable (f a) ν) :
    Integrable (fun ω => ∑ a ∈ s,
      H a ω * ((∑ n ∈ Finset.range (K ω), f a (Y n ω)) -
        (r : ℝ) * ∫ z, f a z ∂ν)) μ ∧
    (∫ ω, ∑ a ∈ s,
      H a ω * ((∑ n ∈ Finset.range (K ω), f a (Y n ω)) -
        (r : ℝ) * ∫ z, f a z ∂ν) ∂μ) = 0 := by
  classical
  have hRaw : ∀ a ∈ s, Integrable
      (fun ω => H a ω *
        ∑ n ∈ Finset.range (K ω), f a (Y n ω)) μ := by
    intro a ha
    exact poisson_predictable_marked_product_integrable_ws01b
      μ ν (H a) (hHm a ha) (hHi a ha)
      K Y hKm r hKlaw hYm hYL hCountMarks
      (hPast a ha) (f a) (hfm a ha) (hfI a ha)
  have hDet : ∀ a ∈ s, Integrable
      (fun ω => H a ω * ((r : ℝ) * ∫ z, f a z ∂ν)) μ := by
    intro a ha
    exact (hHi a ha).mul_const _
  have hEq (a : ι) :
      (fun ω => H a ω *
        ((∑ n ∈ Finset.range (K ω), f a (Y n ω)) -
          (r : ℝ) * ∫ z, f a z ∂ν)) =
      (fun ω => H a ω *
        (∑ n ∈ Finset.range (K ω), f a (Y n ω)) -
        H a ω * ((r : ℝ) * ∫ z, f a z ∂ν)) := by
    funext ω
    ring
  have hCent : ∀ a ∈ s, Integrable (fun ω =>
      H a ω * ((∑ n ∈ Finset.range (K ω), f a (Y n ω)) -
        (r : ℝ) * ∫ z, f a z ∂ν)) μ := by
    intro a ha
    rw [hEq]
    exact (hRaw a ha).sub (hDet a ha)
  constructor
  · exact integrable_finset_sum s (fun a ha => hCent a ha)
  · rw [integral_finset_sum s (fun a ha => hCent a ha)]
    apply Finset.sum_eq_zero
    intro a ha
    rw [hEq, integral_sub (hRaw a ha) (hDet a ha)]
    rw [poisson_predictable_marked_compensation_closed_ws01b
      μ ν (H a) (hHm a ha) (hHi a ha)
      K Y hKm r hKlaw hYm hYL hCountMarks
      (hPast a ha) (f a) (hfm a ha) (hfI a ha)]
    rw [integral_mul_const]
    ring
