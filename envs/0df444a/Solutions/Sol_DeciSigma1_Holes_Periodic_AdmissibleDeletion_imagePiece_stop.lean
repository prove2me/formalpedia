-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:41:56.596268+00:00
-- url     : https://prove2.me/submissions/d06ad8bd-b885-4d2d-ab7d-ff9f4958f170

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
theorem _root_.solution (P : Piece W ρ.length) :
    (hx.imagePiece P).stop = keepCut W ρ N x P.coordinate P.stop := rfl
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
