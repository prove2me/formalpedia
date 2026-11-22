-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.editedTuple_firstRejection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:47.598961+00:00
-- url     : https://prove2.me/submissions/98dcf7f7-fd71-43d4-969b-69b3e3b5b70f

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_deletedPositions_lt_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_editedTuple_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_firstRejection_deletePositions


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
theorem _root_.solution (M : StructuralReader α S k) (hW : M.IsHole W)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) (l : Fin k) :
    M.firstRejection (editedTuple W ρ (Fintype.card S) x) l =
      keepCut W ρ (Fintype.card S) x l (M.firstRejection W l) :=
  firstRejection_deletePositions M (hW.1 l) rfl
    (fun h => absurd (hx.deletedPositions_lt_length h) (lt_irrefl _))
    (hx.runPrefix_editedTuple_greatestPreimage M.toTable rfl l)
end DeciSigma1.Holes.Periodic
