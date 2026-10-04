-- Prove2me | solution 2 for Conway99.conway_99_adjacency_matrix_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:36:49.567164+00:00
-- url     : https://prove2.me/submissions/709b8ac0-2b8a-48d2-b329-56455dbfc636
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Conway99Formal_Coclique22Server_cq09_simultaneous_equivalence_20261003
import Theorems.Thm_Conway99Formal_Coclique22Server_cq10_simultaneous_packet_exists_20261003

set_option autoImplicit false
open scoped BigOperators

private theorem conway99_matrix_of_srg
    (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    ∃ A : Matrix (Fin 99) (Fin 99) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i j, A i j = A j i) ∧
      (∀ i, A i i = 0) ∧
      (∀ i j, (∑ k, A i k * A k j) + A i j =
        (if i = j then 12 else 0) + 2) := by
  classical
  refine ⟨G.adjMatrix ℕ, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : G.Adj i j <;>
      simp [SimpleGraph.adjMatrix_apply, hij]
  · intro i j
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  · intro i
    simp [SimpleGraph.adjMatrix_apply]
  · intro i j
    have htwo :
        (∑ k, G.adjMatrix ℕ i k * G.adjMatrix ℕ k j) =
          Fintype.card (G.commonNeighbors i j) := by
      calc
        _ = (G.adjMatrix ℕ * G.adjMatrix ℕ) i j :=
          Matrix.mul_apply.symm
        _ = (G.adjMatrix ℕ ^ 2) i j := by rw [sq]
        _ = Fintype.card {p : G.Walk i j // p.length = 2} :=
          G.adjMatrix_pow_apply_eq_card_walk (α := ℕ) 2 i j
        _ = Fintype.card (G.commonNeighbors i j) :=
          Fintype.card_congr (G.walkLengthTwoEquivCommonNeighbors i j)
    rw [htwo]
    by_cases hij : i = j
    · subst j
      have hdegree : Fintype.card (G.commonNeighbors i i) = G.degree i := by
        simp [SimpleGraph.commonNeighbors, SimpleGraph.degree,
          SimpleGraph.neighborFinset_def]
      rw [hdegree, h.regular.degree_eq i]
      simp [SimpleGraph.adjMatrix_apply]
    · by_cases hadj : G.Adj i j
      · rw [h.of_adj i j hadj]
        simp [SimpleGraph.adjMatrix_apply, hadj, hij]
      · rw [h.of_not_adj hij hadj]
        simp [SimpleGraph.adjMatrix_apply, hadj, hij]

theorem solution :
    ∃ A : Matrix (Fin 99) (Fin 99) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i j, A i j = A j i) ∧
      (∀ i, A i i = 0) ∧
      (∀ i j, (∑ k, A i k * A k j) + A i j =
        (if i = j then 12 else 0) + 2) := by
  classical
  have hpacket : Nonempty Conway99Formal.Coclique22.SimultaneousCompletion :=
    Conway99Formal.Coclique22Server.cq10_simultaneous_packet_exists_20261003
  have hgraph : Conway99Formal.Coclique22.HasCoclique99 :=
    Conway99Formal.Coclique22Server.cq09_simultaneous_equivalence_20261003.mp
      hpacket
  rcases hgraph with ⟨G, h, _⟩
  exact conway99_matrix_of_srg G h
