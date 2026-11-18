-- Prove2me | solution 1 for CompDesign.thm_5_1_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:35:19.833707+00:00
-- url     : https://prove2.me/submissions/80d04c78-ef16-44d7-bb9f-d3517092641a

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0)
    (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (S T : Finset (Fin n)) :
    v T ≤ v (S ∪ T) ∧ v (S ∪ T) ≤ v S + ∑ i ∈ T \ S, (v (insert i S) - v S) := by
  refine ⟨hm T _ Finset.subset_union_right, ?_⟩
  have key : ∀ U : Finset (Fin n), Disjoint U S →
      v (S ∪ U) ≤ v S + ∑ i ∈ U, (v (insert i S) - v S) := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _; simp
    | insert j U hj ih =>
      intro hd
      have hjS : j ∉ S := fun h => Finset.disjoint_left.1 hd (Finset.mem_insert_self j U) h
      have hdU : Disjoint U S := Finset.disjoint_of_subset_left (Finset.subset_insert j U) hd
      have hjSU : j ∉ S ∪ U := by
        intro h
        rcases Finset.mem_union.1 h with h | h
        · exact hjS h
        · exact hj h
      have hsub := hs S (S ∪ U) j Finset.subset_union_left hjSU
      have e : S ∪ insert j U = insert j (S ∪ U) := Finset.union_insert j S U
      rw [e, Finset.sum_insert hj]
      have := ih hdU
      linarith
  have := key (T \ S) Finset.sdiff_disjoint
  rwa [Finset.union_sdiff_self_eq_union] at this
