-- Prove2me | solution 1 for Concentration.hoeffding_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T06:15:32.429825+00:00
-- url     : https://prove2.me/submissions/4c5e4eb7-8c96-4965-a296-de9a9b524f34

import Mathlib

set_option maxHeartbeats 1000000
set_option linter.all false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- **Generic two-sided Hoeffding.**  For a family `X` of independent random
variables with `X i` a.e. in `[lo i, hi i]`, the sum `∑ X i` concentrates around
its mean `∑ μ[X i]` with sub-Gaussian tails. -/
theorem hoeffding_two_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {lo hi : ι → ℝ}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (lo i) (hi i)) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i ∈ s, X i ω) - ∑ i ∈ s, μ[X i]|}
      ≤ 2 * Real.exp (-ε ^ 2 /
          (2 * ((∑ i ∈ s, (‖hi i - lo i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  set c : ι → ℝ≥0 := fun i => (‖hi i - lo i‖₊ / 2) ^ 2 with hc
  set m : ι → ℝ := fun i => μ[X i] with hm
  have hYsub : ∀ i, HasSubgaussianMGF (fun ω => X i ω - m i) (c i) μ :=
    fun i => hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_bdd i)
  have hYindep : iIndepFun (fun i ω => X i ω - m i) μ :=
    h_indep.comp (fun i t => t - m i) (fun i => by fun_prop)
  have hNYindep : iIndepFun (fun i ω => -(X i ω - m i)) μ :=
    hYindep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hUp := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := s) hYindep
    (fun i _ => hYsub i) hε
  have hLo := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := s) hNYindep
    (fun i _ => (hYsub i).neg) hε
  have hset : {ω | ε ≤ |(∑ i ∈ s, X i ω) - ∑ i ∈ s, m i|}
      = {ω | ε ≤ ∑ i ∈ s, (X i ω - m i)}
        ∪ {ω | ε ≤ ∑ i ∈ s, -(X i ω - m i)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    constructor
    · intro h
      rcases abs_choice ((∑ i ∈ s, X i ω) - ∑ i ∈ s, m i) with hch | hch
      · exact Or.inl (hch ▸ h)
      · exact Or.inr (hch ▸ h)
    · rintro (h | h)
      · exact le_trans h (le_abs_self _)
      · exact le_trans h (neg_le_abs _)
  rw [hset]
  calc
    μ.real ({ω | ε ≤ ∑ i ∈ s, (X i ω - m i)}
        ∪ {ω | ε ≤ ∑ i ∈ s, -(X i ω - m i)})
      ≤ μ.real {ω | ε ≤ ∑ i ∈ s, (X i ω - m i)}
        + μ.real {ω | ε ≤ ∑ i ∈ s, -(X i ω - m i)} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ s, c i : ℝ≥0) : ℝ)))
        + Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ s, c i : ℝ≥0) : ℝ))) := add_le_add hUp hLo
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ s, c i : ℝ≥0) : ℝ))) := by ring

end Salt.Entropy.Chowla


theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {lo hi : ι → ℝ}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (lo i) (hi i)) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i ∈ s, X i ω) - ∑ i ∈ s, μ[X i]|}
      ≤ 2 * Real.exp (-ε ^ 2 /
          (2 * ((∑ i ∈ s, (‖hi i - lo i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) :=
  Salt.Entropy.Chowla.hoeffding_two_sided h_indep h_meas h_bdd hε
