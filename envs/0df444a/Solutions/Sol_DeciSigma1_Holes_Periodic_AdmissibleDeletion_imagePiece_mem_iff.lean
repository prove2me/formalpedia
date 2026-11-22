-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:18.263796+00:00
-- url     : https://prove2.me/submissions/08c21279-1539-4b16-a288-ab431905192f

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_root
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf


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
theorem _root_.solution (P : Piece W ρ.length) :
    hx.imagePiece P ∈ piecesOf (editedTuple W ρ N x) ρ ↔ P ∈ piecesOf W ρ := by
  rw [mem_piecesOf, mem_piecesOf, imagePiece_root]
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
