-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.retainedLength_ge_fixedMargin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:43.783795+00:00
-- url     : https://prove2.me/submissions/066408f8-3e45-4962-ae39-4e72241cf05e

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces

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
    Periodic.fixedMargin N ρ.length ≤ retainedLength (N := N) (x := x) P := by
  unfold retainedLength; have := hx.long P (hx.supp P hxP) hxP; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
