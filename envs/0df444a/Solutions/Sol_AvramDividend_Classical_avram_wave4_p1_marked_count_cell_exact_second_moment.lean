-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_marked_count_cell_exact_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:16:11.358661+00:00
-- url     : https://prove2.me/submissions/78d88449-060e-4a34-9a4d-82fcb4837154

import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_iid_mark_fixed_sum_second_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- Conditional count-cell quadratic compensation without an assumed
conditional expectation or martingale law: the count event factors from the
iid mark-block square. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    (∫ ω in {ω | K ω = j},
      (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) =
      μ.real {ω | K ω = j} *
        ((j : ℝ) * ∫ z, f z ^ 2 ∂ν +
          (j : ℝ) * ((j : ℝ) - 1) * (∫ z, f z ∂ν) ^ 2) := by
  have hmeas : MeasurableSet {ω | K ω = j} :=
    hKm (measurableSet_singleton j)
  have hXmeas : Measurable (fun ω (n : ℕ) => Y n ω) :=
    measurable_pi_lambda _ hYm
  have hψ : Measurable
      (fun xs : ℕ → E => (∑ n ∈ Finset.range j, f (xs n)) ^ 2) := by
    fun_prop
  have hrw : ({ω | K ω = j}).indicator
      (fun ω => (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2) =
      fun ω => (if K ω = j then (1 : ℝ) else 0) *
        (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : K ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hrw]
  have hmean :
      (∫ ω, (if K ω = j then (1 : ℝ) else 0) ∂μ) =
        μ.real {ω | K ω = j} := by
    have hconst : (fun ω => if K ω = j then (1 : ℝ) else 0) =
        ({ω | K ω = j}).indicator (fun _ => 1) := by
      funext ω
      by_cases h : K ω = j <;> simp [Set.mem_setOf_eq, h]
    rw [hconst, integral_indicator_const (1 : ℝ) hmeas]
    simp
  rw [show
      (∫ ω,
        (if K ω = j then (1 : ℝ) else 0) *
          (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) =
        (∫ ω, if K ω = j then (1 : ℝ) else 0 ∂μ) *
        (∫ ω, (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) from
    hCountMarks.integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0)
      (g := fun xs : ℕ → E => (∑ n ∈ Finset.range j, f (xs n)) ^ 2)
      hKm.aemeasurable hXmeas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ.aestronglyMeasurable]
  rw [hmean, avram_wave4_p1_iid_mark_fixed_sum_second_moment
    μ ν Y hYm hYL hYi f hf hfI hf2 j]
