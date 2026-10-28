-- Prove2me | solution 1 for AvramDividend.Classical.poisson_independent_count_cell_mark_mean_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:08:33.40547+00:00
-- url     : https://prove2.me/submissions/84bae3be-bee4-48ce-8a04-bd1152d5917b

import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_identically_law_fixed_marks_expectation_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- True count-cell compensation for random marks independent of the count:
the count event factors from its fixed-length mark sum. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) :
    (∫ ω in {ω | K ω = j},
      ∑ n ∈ Finset.range j, f (Y n ω) ∂μ) =
      μ.real {ω | K ω = j} *
        ((j : ℝ) * ∫ y, f y ∂ν) := by
  have hmeas : MeasurableSet {ω | K ω = j} :=
    hKm (measurableSet_singleton j)
  have hXmeas : Measurable (fun ω (n : ℕ) => Y n ω) :=
    measurable_pi_lambda _ hYm
  have hψ : Measurable
      (fun xs : ℕ → E => ∑ n ∈ Finset.range j, f (xs n)) := by
    fun_prop
  have hrw : ({ω | K ω = j}).indicator
      (fun ω => ∑ n ∈ Finset.range j, f (Y n ω)) =
      fun ω => (if K ω = j then (1 : ℝ) else 0) *
        (∑ n ∈ Finset.range j, f (Y n ω)) := by
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
            (∑ n ∈ Finset.range j, f (Y n ω)) ∂μ) =
      (∫ ω, if K ω = j then (1 : ℝ) else 0 ∂μ) *
      (∫ ω, ∑ n ∈ Finset.range j, f (Y n ω) ∂μ) from
    hIndep.integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0)
      (g := fun xs : ℕ → E => ∑ n ∈ Finset.range j, f (xs n))
      hKm.aemeasurable hXmeas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ.aestronglyMeasurable]
  rw [hmean, identically_law_fixed_marks_expectation_ws01b
    μ ν Y hYm hYL j f hf hfI]
