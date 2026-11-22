-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.editedTuple_endState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:47.141183+00:00
-- url     : https://prove2.me/submissions/8041974e-72c7-41f8-b25b-24afe1091d90

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_editedTuple
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_deletedPositions_lt_length
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
variable [Fintype S] (T : Table α S k) (hN : N = Fintype.card S)
include hN
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution (l : Fin k) : T.endState (editedTuple W ρ N x) l = T.endState W l := by
  unfold endState
  rw [show (editedTuple W ρ N x l).length = keepCut W ρ N x l (W l).length by
    rw [editedTuple, length_deletePositions]; rfl]
  exact hx.runPrefix_editedTuple T hN l le_rfl
      (Or.inr (Or.inl fun h => absurd (hx.deletedPositions_lt_length h)
    (lt_irrefl _)))
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
