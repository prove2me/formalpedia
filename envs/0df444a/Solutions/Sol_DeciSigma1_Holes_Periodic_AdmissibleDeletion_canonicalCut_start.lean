-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:53.993847+00:00
-- url     : https://prove2.me/submissions/11227fb8-08d6-4f52-8a8b-d24376570558

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_start_lt_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin


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
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) P.coordinate P.start (hx.imagePiece P).start :=
  ⟨by have := P.start_lt_stop; have := P.stop_le_length; omega, rfl,
      fun _ => hx.in_piece_not_mem P le_rfl
    P.start_lt_stop (Or.inl
        (by have := Periodic.d_le_boundaryMargin N ρ.length; have := P.period_pos; omega))⟩
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
