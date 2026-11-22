-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_editedTuple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:46.592095+00:00
-- url     : https://prove2.me/submissions/7bf53b3c-ace0-422e-88ef-0f835e4fbaca

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_block_states
public import Theorems.Thm_DeciSigma1_Words_deletePositions_take
public import Theorems.Thm_DeciSigma1_Words_runFrom_deletePositions_take


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
theorem _root_.solution (l : Fin k) {c : ℕ} (hc : c ≤ (W l).length)
    (hint : c = 0 ∨ c ∉ deletedPositions W ρ N x l ∨ c - 1 ∉ deletedPositions W ρ N x l) :
    T.runPrefix (editedTuple W ρ N x) l (keepCut W ρ N x l c) = T.runPrefix W l c := by
  unfold runPrefix keepCut editedTuple
  rw [deletePositions_take _ hc]
  exact runFrom_deletePositions_take T _ _ (hx.block_states T hN l) c hc hint
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
