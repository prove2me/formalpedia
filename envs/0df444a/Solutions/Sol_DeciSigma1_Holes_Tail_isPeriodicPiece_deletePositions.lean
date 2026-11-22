-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.isPeriodicPiece_deletePositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:43.390823+00:00
-- url     : https://prove2.me/submissions/6e5cbfca-a52a-4955-a98d-e99c5efb9baa

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Theorems.Thm_DeciSigma1_Holes_Periodic_isPeriodicPiece_deletePositions_with_root


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {U U' : Fin k → List α} {l : Fin k}
    {Dl : Finset ℕ}
    (hU' : U' l = deletePositions (U l) Dl) {d s e : ℕ} (hc : IsPeriodicPiece U d l s e)
    (hin : ∀ p, s ≤ p → p < e → p ∉ Dl) (hleft : s ≠ 0 → s - 1 ∉ Dl)
    (hright : e < (U l).length → e ∉ Dl) :
    IsPeriodicPiece U' d l (retainedCount Dl s) (retainedCount Dl e) ∧ retainedCount Dl e =
        retainedCount Dl s + (e - s) := by
  obtain ⟨hpiece, hlength, -⟩ :=
    isPeriodicPiece_deletePositions_with_root hU' hc hin hleft hright
  exact ⟨hpiece, hlength⟩
end DeciSigma1.Holes.Tail
