-- Prove2me | solution 1 for ConsistentSubmodular.sum_weight_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:16.418204+00:00
-- url     : https://prove2.me/submissions/90c66530-7201-4d25-99d3-14250b2a6977

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (p : ι → ℝ) (L : Finset ι) :
    (∑ S : Finset ι, if Disjoint S L then bernoulliWeight p S else 0) =
      ∏ i ∈ L, (1 - p i) := by
  classical
  have hterm (S : Finset ι) :
      (if Disjoint S L then bernoulliWeight p S else 0) =
        (∏ i ∈ S, if i ∈ L then 0 else p i) * ∏ i ∈ Sᶜ, (1 - p i) := by
    by_cases hd : Disjoint S L
    · rw [if_pos hd]
      unfold bernoulliWeight
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.disjoint_left.mp hd hi]
    · rw [if_neg hd]
      obtain ⟨i, hi⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hd
      have hzero : (∏ i ∈ S, if i ∈ L then (0 : ℝ) else p i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_inter.mp hi).1 (by simp [(Finset.mem_inter.mp hi).2])
      rw [hzero, zero_mul]
  simp_rw [hterm]
  rw [← Fintype.prod_add]
  have hpoint (i : ι) : (if i ∈ L then (0 : ℝ) else p i) + (1 - p i) =
      if i ∈ L then 1 - p i else 1 := by split_ifs <;> ring
  simp_rw [hpoint]
  exact Finset.prod_ite_mem_eq L (fun i => 1 - p i)

end
