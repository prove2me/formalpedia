-- Prove2me | solution 1 for Conway99.conway_99
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T19:41:10.606034+00:00
-- url     : https://prove2.me/submissions/391dd5e6-f444-4621-a683-a41109d44a99
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Theorems.Thm_Conway99_conway_99_adjacency_matrix_exists

open SimpleGraph Finset

theorem solution : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α)
    (_ : DecidableRel g.Adj), IsSRGWith g 99 14 1 2 := by
  obtain ⟨A, h01, hsymm, hdiag, hsq⟩ := Conway99.conway_99_adjacency_matrix_exists
  classical
  set g : SimpleGraph (Fin 99) :=
    { Adj := fun i j => A i j = 1
      symm := by
        have h : ∀ i j : Fin 99, A i j = 1 → A j i = 1 := by
          intro i j hij
          rw [hsymm j i]
          exact hij
        first
        | exact h
        | exact ⟨h⟩
      loopless := by
        have h : ∀ i : Fin 99, ¬ (A i i = 1) := by
          intro i
          rw [hdiag i]
          norm_num
        first
        | exact h
        | exact ⟨h⟩ } with hg
  have hadj : ∀ i j, g.Adj i j ↔ A i j = 1 := fun i j => Iff.rfl
  -- the number of common neighbours of `i` and `j` is the `(i, j)` entry of `A ^ 2`
  have key : ∀ i j, Fintype.card (g.commonNeighbors i j) = ∑ k, A i k * A k j := by
    intro i j
    rw [← Set.toFinset_card]
    have hset : (g.commonNeighbors i j).toFinset
        = Finset.univ.filter (fun k => A i k = 1 ∧ A j k = 1) := by
      ext k
      simp [SimpleGraph.mem_commonNeighbors, hadj]
    rw [hset, Finset.card_filter]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hsymm k j]
    rcases h01 i k with h1 | h1 <;> rcases h01 j k with h2 | h2 <;>
      simp [h1, h2]
  have hdeg : ∀ i, g.degree i = 14 := by
    intro i
    have h1 : g.degree i = Fintype.card (g.commonNeighbors i i) := by
      rw [← Set.toFinset_card, ← card_neighborFinset_eq_degree]
      congr 1
      ext k
      simp [SimpleGraph.mem_commonNeighbors, hadj]
    have h2 := hsq i i
    rw [hdiag i, if_pos rfl] at h2
    rw [h1, key i i]
    omega
  refine ⟨Fin 99, inferInstance, g, inferInstance, ?_⟩
  refine ⟨by simp, hdeg, ?_, ?_⟩
  · intro v w hvw
    have hne : v ≠ w := g.ne_of_adj hvw
    have h2 := hsq v w
    rw [if_neg hne, (hadj v w).1 hvw] at h2
    rw [key v w]
    omega
  · intro v w hne hnadj
    have h0 : A v w = 0 := by
      rcases h01 v w with h | h
      · exact h
      · exact absurd ((hadj v w).2 h) hnadj
    have h2 := hsq v w
    rw [if_neg hne, h0] at h2
    rw [key v w]
    omega
