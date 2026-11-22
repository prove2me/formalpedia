-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:37.13063+00:00
-- url     : https://prove2.me/submissions/95e2b297-5d26-4757-800d-bb15847c0f9f

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_length_editedTuple
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono


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
omit hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {l : Fin k} {c c' : ℕ} (h :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c') :
    c' ≤ (editedTuple W ρ N x l).length := by
  rw [← h.2.1, length_editedTuple]; exact retainedCount_mono h.1
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
