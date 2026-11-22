-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_hole_rejectedTailLength_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:10:43.768992+00:00
-- url     : https://prove2.me/submissions/9dfe09ab-109f-4c9c-8794-0a88759ce37c

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_tail_le_compressionLengthBound
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_with_run_cover


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (M : StructuralReader α S k) {W : Fin k → List α}
    (hW : M.IsHole W) :
    ∃ W', M.IsHole W' ∧ ∀ i, M.Immortal (M.endState W' i) →
      M.rejectedTailLength W' i ≤ tailLengthBound (Fintype.card α) k (Fintype.card S) := by
  obtain ⟨W', hW', hcov⟩ :=
    exists_hole_with_run_cover (levelBounds (Fintype.card α) k (Fintype.card S)) hW
  exact exists_hole_tail_le_compressionLengthBound M hW' hcov
end DeciSigma1.Holes.Tail
