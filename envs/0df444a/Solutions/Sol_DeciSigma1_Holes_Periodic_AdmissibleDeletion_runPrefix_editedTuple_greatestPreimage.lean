-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_editedTuple_greatestPreimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:46.425802+00:00
-- url     : https://prove2.me/submissions/a344963d-1399-4efc-aaea-c94c85a4304e

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_block_states
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_deletedPositions_lt_length
public import Theorems.Thm_DeciSigma1_Words_runFrom_take_deletePositions


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
theorem _root_.solution (l : Fin k) (a : ℕ) :
    T.runPrefix (editedTuple W ρ N x) l a =
      T.runPrefix W l (greatestPreimage (deletedPositions W ρ N x l) a) :=
  runFrom_take_deletePositions T _ _ (hx.block_states T hN l)
    (fun h => absurd (hx.deletedPositions_lt_length h) (lt_irrefl _)) a
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
