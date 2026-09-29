-- Prove2me | solution 1 for Conway99.srg_9_4_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T16:57:00.987724+00:00
-- url     : https://prove2.me/submissions/801d90dd-00eb-474c-a6d8-b1281b585692

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph

/-- The `3 × 3` rook's graph: two distinct cells of a `3 × 3` grid are adjacent
when they share a row or share a column. -/
private def rook : SimpleGraph (Fin 3 × Fin 3) :=
  SimpleGraph.fromRel fun a b => a.1 = b.1 ∨ a.2 = b.2

private instance rookDec : DecidableRel rook.Adj := fun a b =>
  decidable_of_iff (a ≠ b ∧ ((a.1 = b.1 ∨ a.2 = b.2) ∨ (b.1 = a.1 ∨ b.2 = a.2)))
    Iff.rfl

theorem solution : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α)
    (_ : DecidableRel g.Adj), IsSRGWith g 9 4 1 2 := by
  refine ⟨Fin 3 × Fin 3, inferInstance, rook, rookDec, ?_, ?_, ?_, ?_⟩
  · decide
  · show ∀ v : Fin 3 × Fin 3, rook.degree v = 4
    decide
  · decide
  · show ∀ v w : Fin 3 × Fin 3, v ≠ w →
      ¬rook.Adj v w → Fintype.card (rook.commonNeighbors v w) = 2
    decide
