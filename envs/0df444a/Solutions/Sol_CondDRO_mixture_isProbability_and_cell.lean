-- Prove2me | solution 1 for CondDRO.mixture_isProbability_and_cell
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:17:38.827445+00:00
-- url     : https://prove2.me/submissions/fa628e14-bc65-43c9-9ac4-f7a937800748

import Mathlib
import Definitions.Def_CondDRO_FinitePartition
import Definitions.Def_CondDRO_mixture

open MeasureTheory

open CondDRO in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : FinitePartition Ω I) (A : I → Set (Measure Ω))
    (hA_prob : ∀ i, ∀ Q ∈ A i, IsProbabilityMeasure Q)
    (hA_supp : ∀ i, ∀ Q ∈ A i, Q (ϖ.cell i)ᶜ = 0)
    (ν : I → ℝ) (hν_pos : ∀ i, 0 < ν i) (hν_sum : ∑ i, ν i = 1) :
    ∀ Q ∈ mixture A ν,
      IsProbabilityMeasure Q ∧ ∀ i, Q (ϖ.cell i) = ENNReal.ofReal (ν i) := by
  classical
  rintro Q ⟨q, hq, rfl⟩
  have hprob : ∀ j, IsProbabilityMeasure (q j) := fun j => hA_prob j _ (hq j)
  have hcell : ∀ i j, q j (ϖ.cell i) = if i = j then 1 else 0 := by
    intro i j
    split_ifs with h
    · subst h
      exact (prob_compl_eq_zero_iff (ϖ.measurableSet_cell i)).mp (hA_supp i _ (hq i))
    · exact measure_mono_null (ϖ.pairwise_disjoint h).subset_compl_right (hA_supp j _ (hq j))
  refine ⟨⟨?_⟩, fun i => ?_⟩
  · simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hν_pos i).le), hν_sum, ENNReal.ofReal_one]
  · simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul, hcell,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
