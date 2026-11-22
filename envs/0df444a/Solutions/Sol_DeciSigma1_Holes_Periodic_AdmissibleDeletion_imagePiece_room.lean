-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_room
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:42.812801+00:00
-- url     : https://prove2.me/submissions/5e007758-da9f-4bcd-8b84-919f47b5adc1

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop_eq
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_retainedLength_ge_fixedMargin


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
    (hx.imagePiece R).start + 6 * Periodic.boundaryMargin N ρ.length + 2 *
        Periodic.statePeriodModulus N ρ.length ≤ (hx.imagePiece R).stop := by
  have := hx.retainedLength_ge_fixedMargin R hxR; have :=
      hx.imagePiece_stop_eq R; unfold Periodic.fixedMargin at *; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
