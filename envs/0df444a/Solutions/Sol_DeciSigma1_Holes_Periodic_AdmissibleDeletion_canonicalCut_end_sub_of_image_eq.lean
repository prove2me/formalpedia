-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_end_sub_of_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:45.181738+00:00
-- url     : https://prove2.me/submissions/7f27adbf-042c-4159-88e5-7dcdda21648b

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_end_sub


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
theorem _root_.solution {P : Piece W ρ.length}
    {P' : Piece (editedTuple W ρ N x) ρ.length}
    (hP : hx.imagePiece P = P') {l : Fin k} (hl : P'.coordinate = l) :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l (P.stop - ρ.length) (P'.stop - ρ.length)
        := by
  have hPl : P.coordinate = l := by rw [← hl, ← hP]; rfl
  have := hx.canonicalCut_end_sub P; rw [hP, hPl] at this; exact this
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
