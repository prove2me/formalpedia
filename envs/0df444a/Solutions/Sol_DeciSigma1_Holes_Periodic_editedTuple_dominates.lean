-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.editedTuple_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:21.863279+00:00
-- url     : https://prove2.me/submissions/906a129b-f5ed-423b-8927-42853d91677c

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_editedTuple_channel_subset
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_editedTuple_endState
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_editedTuple_visitedStates


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (T : Table α S k)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) :
    Dominates T (editedTuple W ρ (Fintype.card S) x) W :=
  ⟨fun l => hx.editedTuple_endState T rfl l, fun l => hx.editedTuple_visitedStates T rfl l,
    fun i j => editedTuple_channel_subset T hx i j⟩
end DeciSigma1.Holes.Periodic
