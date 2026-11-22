-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_piece_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:28.058809+00:00
-- url     : https://prove2.me/submissions/0f2e7070-345d-4d5b-95d7-1d355328a143

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_mem_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {R : Piece W ρ.length} (hxR : x R ≠ 0) :
    hx.imagePiece R ∈ piecesOf (editedTuple W ρ N x) ρ :=
        (hx.imagePiece_mem_iff R).mpr (hx.supp R hxR)
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
