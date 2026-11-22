-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_start_of_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:46.006456+00:00
-- url     : https://prove2.me/submissions/929b87c6-6bd1-4805-a045-4d7f7984536b

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_start


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
    (hP : hx.imagePiece P = P') {l : Fin k}
        (hl : P'.coordinate = l) :
            CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l P.start P'.start := by
  have hPl : P.coordinate = l := by rw [← hl, ← hP]; rfl
  have := hx.canonicalCut_start P; rw [hP, hPl] at this; exact this
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
