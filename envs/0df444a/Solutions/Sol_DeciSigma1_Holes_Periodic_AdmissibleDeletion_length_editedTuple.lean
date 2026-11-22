-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.length_editedTuple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:12.401579+00:00
-- url     : https://prove2.me/submissions/2ac1790e-9633-4b19-bc62-c383375ce9f7

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
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
omit hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution (l : Fin k) :
    (editedTuple W ρ N x l).length = keepCut W ρ N x l (W l).length := by
  rw [editedTuple, length_deletePositions]; rfl
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
