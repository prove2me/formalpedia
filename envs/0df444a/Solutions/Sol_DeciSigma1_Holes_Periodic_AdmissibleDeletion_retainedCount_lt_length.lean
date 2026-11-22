-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.retainedCount_lt_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:26.645167+00:00
-- url     : https://prove2.me/submissions/511a3fb4-1b6d-426d-ade6-1ff681a5040b

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_last_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono


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
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {l : Fin k} {c : ℕ} (hc : c < (W l).length) :
    keepCut W ρ N x l c < keepCut W ρ N x l (W l).length := by
  have :=
      retainedCount_lt_of_not_mem (D := deletedPositions W ρ N x l) (hx.last_not_mem l (by omega))
    (show (W l).length - 1 < (W l).length by omega)
  have := retainedCount_mono (D := deletedPositions W ρ N x l) (show c ≤ (W l).length - 1 by omega)
  unfold keepCut; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
