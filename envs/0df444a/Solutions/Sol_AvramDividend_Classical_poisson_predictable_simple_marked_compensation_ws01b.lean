-- Prove2me | solution 1 for AvramDividend.Classical.poisson_predictable_simple_marked_compensation_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:23:05.316853+00:00
-- url     : https://prove2.me/submissions/451ff679-6ae6-4871-bb9e-5e7455fc33a1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_campbell_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- A genuine predictable-simple Campbell compensation: the past weight is
independent of the joint future Poisson count and mark family. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E)
    (H : Ω → ℝ) (hHm : Measurable H) (hHi : Integrable H μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun H
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν)
    (hKernel : Measurable
      (fun p : ℕ × (ℕ → E) =>
        ∑ n ∈ Finset.range p.1, f (p.2 n))) :
    (∫ ω, H ω * (∑ n ∈ Finset.range (K ω), f (Y n ω)) ∂μ) =
      (∫ ω, H ω ∂μ) * ((r : ℝ) * ∫ y, f y ∂ν) := by
  let Z : Ω → ℕ × (ℕ → E) :=
    fun ω => (K ω, fun n => Y n ω)
  let g : ℕ × (ℕ → E) → ℝ :=
    fun p => ∑ n ∈ Finset.range p.1, f (p.2 n)
  have hZm : Measurable Z := by
    exact hKm.prod (measurable_pi_lambda _ hYm)
  have hgm : Measurable g := hKernel
  have hGm : Measurable (g ∘ Z) := hgm.comp hZm
  have hIndepG : IndepFun H (g ∘ Z) μ :=
    hPast.comp measurable_id hgm
  have hfac :
      (∫ ω, H ω * (g (Z ω)) ∂μ) =
        (∫ ω, H ω ∂μ) *
          (∫ ω, g (Z ω) ∂μ) := by
    exact hIndepG.integral_fun_comp_mul_comp
      (f := fun a : ℝ => a)
      (g := fun a : ℝ => a)
      hHm.aemeasurable hGm.aemeasurable
      measurable_id.aestronglyMeasurable
      measurable_id.aestronglyMeasurable
  calc
    (∫ ω, H ω *
        (∑ n ∈ Finset.range (K ω), f (Y n ω)) ∂μ) =
        (∫ ω, H ω ∂μ) *
          (∫ ω, ∑ n ∈ Finset.range (K ω), f (Y n ω) ∂μ) := by
            simpa [g, Z, Function.comp_def] using hfac
    _ = (∫ ω, H ω ∂μ) *
          ((r : ℝ) * ∫ y, f y ∂ν) := by
      rw [poisson_random_mark_sum_campbell_ws01b
        μ ν K Y hKm r hKlaw hYm hYL hCountMarks f hf hfI]
