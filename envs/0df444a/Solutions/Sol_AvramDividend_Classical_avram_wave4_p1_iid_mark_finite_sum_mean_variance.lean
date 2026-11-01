-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_iid_mark_finite_sum_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:48:49.293991+00:00
-- url     : https://prove2.me/submissions/fd62024f-fb34-48db-8c88-43a4b57ff9c1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

/-- Independent identically distributed marks have exactly additive
second-order variance and the expected finite-sum mean. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → E) (hYm : ∀ i, Measurable (Y i))
    (hYL : ∀ i, HasLaw (Y i) ν P)
    (hYi : iIndepFun Y P)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν)
    (s : Finset ℕ) :
    (∫ ω, ∑ i ∈ s, f (Y i ω) ∂P) =
      (s.card : ℝ) * ∫ z, f z ∂ν ∧
    variance (fun ω => ∑ i ∈ s, f (Y i ω)) P =
      (s.card : ℝ) * variance f ν := by
  have hXi : ∀ i, MemLp (fun ω => f (Y i ω)) 2 P := by
    intro i
    simpa [Function.comp_def] using
      hf2.comp_measurePreserving ((hYL i).measurePreserving (hYm i))
  have hXiInt : ∀ i, Integrable (fun ω => f (Y i ω)) P := by
    intro i
    have hi : Integrable f (Measure.map (Y i) P) := by
      rwa [(hYL i).map_eq]
    exact hi.comp_measurable (hYm i)
  have hMeanI : ∀ i, (∫ ω, f (Y i ω) ∂P) = ∫ z, f z ∂ν := by
    intro i
    simpa [Function.comp_def] using
      (hYL i).integral_comp hf.aestronglyMeasurable
  have hPair : Set.Pairwise (↑s : Set ℕ)
      (fun i j => IndepFun (fun ω => f (Y i ω)) (fun ω => f (Y j ω)) P) := by
    intro i hi j hj hij
    simpa [Function.comp_def] using (hYi.indepFun hij).comp hf hf
  have hVarI : ∀ i, variance (fun ω => f (Y i ω)) P = variance f ν := by
    intro i
    simpa [Function.comp_def] using
      ((hYL i).measurePreserving (hYm i)).variance_fun_comp hf.aemeasurable
  constructor
  · rw [integral_finset_sum s (fun i hi => hXiInt i)]
    simp_rw [hMeanI]
    simp [nsmul_eq_mul]
  · have hSum := ProbabilityTheory.IndepFun.variance_sum
      (X := fun i ω => f (Y i ω)) (s := s) (fun i hi => hXi i) hPair
    have hPointwise :
        (∑ i ∈ s, (fun ω => f (Y i ω))) =
          (fun ω => ∑ i ∈ s, f (Y i ω)) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hPointwise] at hSum
    rw [hSum]
    simp_rw [hVarI]
    simp [nsmul_eq_mul]
