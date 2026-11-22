-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_hole_tail_le_compressionLengthBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:26.287227+00:00
-- url     : https://prove2.me/submissions/aeec7efb-7244-4515-8ca0-59f7fc5d38e0

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_tail_le_compressionLengthBoundIter

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (M : StructuralReader α S k) {W : Fin k → List α}
    (hW : M.IsHole W) {R D E : ℕ} (hcov : HasScaledRunCover M W R D E) :
    ∃ W', M.IsHole W' ∧ ∀ i, M.Immortal (M.endState W' i) → M.rejectedTailLength W' i ≤
      compressionLengthBound k (Fintype.card S) R D E :=
  exists_hole_tail_le_compressionLengthBoundIter M D (k * R) W E hW hcov
end DeciSigma1.Holes.Tail
