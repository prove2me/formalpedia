-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.nojun_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:40.375846+00:00
-- url     : https://prove2.me/submissions/ad476938-ccae-4407-bce2-a623e5efd86d

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_room
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_sep
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


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
theorem _root_.solution (P' : Piece (editedTuple W ρ N x) ρ.length) (m : ℕ) :
    hx.NoInteriorJunction P'.coordinate (P'.stop - ρ.length) m := by
  intro R hRl hxR h1 h2
  exfalso
  have hroom := hx.imagePiece_room hxR
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hR'l : (hx.imagePiece R).coordinate = P'.coordinate := hRl
  by_cases hRP : hx.imagePiece R = P'
  · have hs : (hx.imagePiece R).start = P'.start := by rw [hRP]
    have he : (hx.imagePiece R).stop = P'.stop := by rw [hRP]
    omega
  · rcases le_total (hx.imagePiece R).start P'.start with h | h
    · have := Piece.sep hRP hR'l h; have := P'.long; omega
    · have := Piece.sep (Ne.symm hRP) hR'l.symm h; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
