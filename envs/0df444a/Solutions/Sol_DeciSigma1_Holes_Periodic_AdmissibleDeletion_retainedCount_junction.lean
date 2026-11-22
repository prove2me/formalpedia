-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.retainedCount_junction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:17.238804+00:00
-- url     : https://prove2.me/submissions/a000f5e7-82bc-47a2-be5e-e493ac684def

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound


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
theorem _root_.solution (P : Piece W ρ.length) (hxP : x P ≠ 0) :
    keepCut W ρ N x P.coordinate (P.start + Periodic.boundaryMargin N ρ.length) =
        (hx.imagePiece P).start + Periodic.boundaryMargin N ρ.length := by
  rw [hx.retainedCount_head P (Or.inl le_rfl)
      (by have := hx.site_bound hxP; unfold Piece.len; omega)]
  rfl
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
