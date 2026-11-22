-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.exists_canonicalCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:05.265219+00:00
-- url     : https://prove2.me/submissions/d4cb121d-79fe-43c3-b5a5-9594c80c5a76

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_deletedPositions_lt_length
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_le_length
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage



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
theorem _root_.solution (l : Fin k) {c' : ℕ} (hc' : c' ≤ (editedTuple W ρ N x l).length) :
    ∃ c, CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c' :=
  ⟨greatestPreimage (deletedPositions W ρ N x l) c',
    greatestPreimage_le_length _
        (fun h => absurd (hx.deletedPositions_lt_length h) (lt_irrefl _)) hc',
    retainedCount_greatestPreimage c', fun _ => greatestPreimage_not_mem c'⟩
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
