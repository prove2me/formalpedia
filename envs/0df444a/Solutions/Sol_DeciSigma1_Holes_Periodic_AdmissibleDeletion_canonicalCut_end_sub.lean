-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_end_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:57.148874+00:00
-- url     : https://prove2.me/submissions/b6b43947-8cd5-4848-add5-702830cf5a99

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_len_ge
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop

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
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) P.coordinate (P.stop - ρ.length)
        ((hx.imagePiece P).stop - ρ.length) := by
  have hPl := P.start_add_len
  have hd := P.period_pos
  have hnl := hx.retainedLength_ge P
  have hL := retainedLength_le (N := N) (x := x) P
  have hlg := P.len_ge
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hpos : ∀ i < ρ.length, P.stop - ρ.length + i ∉ deletedPositions W ρ N x P.coordinate := by
    intro i hi
    by_cases hxP : x P = 0
    · exact hx.not_mem_deletedPositions_of_piece_margin P (by omega) (by omega)
        (Or.inr (Or.inl hxP))
    · have hb := hx.site_bound hxP
      exact hx.in_piece_not_mem P (by omega) (by omega) (Or.inr (by omega))
  have hk := retainedCount_add_of_not_mem hpos
  rw [show P.stop - ρ.length + ρ.length = P.stop by have := P.long; omega] at hk
  refine ⟨by have := P.stop_le_length; omega, ?_, fun _ => by simpa using hpos 0 hd⟩
  rw [imagePiece_stop]; unfold keepCut; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
