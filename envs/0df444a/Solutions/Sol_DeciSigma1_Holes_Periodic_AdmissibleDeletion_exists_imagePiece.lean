-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.exists_imagePiece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:14.684796+00:00
-- url     : https://prove2.me/submissions/e7a08630-b689-4f2e-a3f8-0fc2faf890ca

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_retainedLength_ge_fixedMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop_eq
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_length_editedTuple
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_exists_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_retainedCount_junction
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_zero_not_mem
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_add
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_len_ge
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_root_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_start_lt_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions
public import Theorems.Thm_DeciSigma1_Holes_Periodic_piece_eq_of_overlap
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
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
theorem _root_.solution (P' : Piece (editedTuple W ρ N x) ρ.length) :
    ∃ P : Piece W ρ.length, hx.imagePiece P = P' := by
  have hd := P'.period_pos
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  by_cases hcase : ∃ R : Piece W ρ.length, R.coordinate = P'.coordinate ∧ x R ≠ 0 ∧
      P'.start ≤ (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ≤ P'.stop
  · obtain ⟨R, hRl, hxR, h1, h2⟩ := hcase
    refine ⟨R, piece_eq_of_overlap hRl (by omega) ?_⟩
    have := hx.imagePiece_stop_eq R
    have := hx.retainedLength_ge_fixedMargin R hxR
    unfold Periodic.fixedMargin at this
    omega
  push Not at hcase
  have hPs : P'.start ≤
      (editedTuple W ρ N x
          P'.coordinate).length := by have := P'.start_lt_stop; have := P'.stop_le_length; omega
  obtain ⟨c, hc⟩ := hx.exists_canonicalCut P'.coordinate hPs
  have hPl := P'.start_add_len
  obtain ⟨hcn, htext⟩ := hx.canonicalCut_add (n := P'.len) hc
    (by have := P'.stop_le_length; omega)
    fun R hRl hxR h => absurd (hcase R hRl hxR (by omega)) (by omega)
  obtain ⟨hcl, hck, hcr⟩ := hc
  obtain ⟨hcnl, hcnk, hcnr⟩ := hcn
  have hlenU := length_editedTuple (W := W) (ρ := ρ) (N := N) (x := x) P'.coordinate
  unfold keepCut at hck hcnk hlenU
  have hcW : c < (W P'.coordinate).length := by
    by_contra hge
    have : c = (W P'.coordinate).length := by omega
    subst this
    have := P'.start_lt_stop; have := P'.stop_le_length; omega
  have hlg := P'.len_ge
  -- the letters of the original stretch
  have hper : ∀ p, c ≤ p → p + ρ.length < c + P'.len → (W P'.coordinate)[p]? =
      (W P'.coordinate)[p + ρ.length]? := by
    intro p hp hpe
    rw [show p = c + (p - c) by omega, htext _ (by omega), Nat.add_assoc,
      htext _ (by omega), ← Nat.add_assoc]
    exact P'.periodic _ (by omega) (by omega)
  have hroot : ((W P'.coordinate).drop c).take ρ.length = P'.root := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < ρ.length
    · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, htext i (by omega), Piece.root,
        List.getElem?_take_of_lt hi, List.getElem?_drop]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
        (by rw [P'.root_length]; omega)]
  have hmaxL : c = 0 ∨ (W P'.coordinate)[c - 1]? ≠ (W P'.coordinate)[c - 1 + ρ.length]? := by
    by_cases hs0 : P'.start = 0
    · left
      by_contra hc0
      have := retainedCount_succ_of_not_mem
        (zero_not_mem (W := W) (ρ := ρ) (N := N) (x := x) (l := P'.coordinate))
      have := retainedCount_mono (D := deletedPositions W ρ N x P'.coordinate) (show 1 ≤ c by omega)
      simp at *; omega
    rcases P'.left_maximal with h | h
    · exact absurd h hs0
    right
    have hc0 : c ≠ 0 := by intro h0; subst h0; simp at hck; omega
    have hcm : c - 1 ∉ deletedPositions W ρ N x P'.coordinate := by
      intro hm
      have hcD := hcr hcW
      obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hm
      have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
      have hend : c = R.start + Periodic.boundaryMargin N ρ.length +
          Periodic.statePeriodModulus N ρ.length * x R := by
        by_contra hne
        exact hcD (by rw [← hRl]; exact hx.site_sub (by omega) (by omega))
      have hj := hx.retainedCount_junction R hxR
      have hkm : keepCut W ρ N x R.coordinate
          (R.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x
              R) =
          keepCut W ρ N x R.coordinate (R.start + Periodic.boundaryMargin N ρ.length) :=
        retainedCount_add_of_mem (fun i hi => hx.site_sub (by omega) (by omega))
      rw [← hend, hRl] at hkm
      rw [hRl] at hj
      unfold keepCut at hj hkm
      exact absurd (hcase R hRl hxR (by omega)) (by have := P'.start_lt_stop; omega)
    have hk1 := retainedCount_succ_of_not_mem hcm
    rw [show c - 1 + 1 = c by omega] at hk1
    rw [← (show (editedTuple W ρ N x P'.coordinate)[P'.start - 1]? = (W P'.coordinate)[c - 1]? by
      rw [show P'.start - 1 = retainedCount (deletedPositions W ρ N x P'.coordinate)
          (c - 1) by omega, editedTuple,
        getElem?_deletePositions _ hcm (by omega)]),
      show c - 1 + ρ.length = c + (ρ.length - 1) by omega, htext _ (by omega),
      show P'.start + (ρ.length - 1) = P'.start - 1 + ρ.length by omega]
    exact h
  have hmaxR : c + P'.len = (W P'.coordinate).length ∨
      (W P'.coordinate)[c + P'.len]? ≠ (W P'.coordinate)[c + P'.len - ρ.length]? := by
    by_cases hE : P'.stop = (editedTuple W ρ N x P'.coordinate).length
    · left
      by_contra hne
      have :=
          retainedCount_lt_of_not_mem (hcnr (by omega))
              (show c + P'.len < (W P'.coordinate).length by omega)
      omega
    rcases P'.right_maximal with h | h
    · exact absurd h hE
    right
    have hlt : c + P'.len < (W P'.coordinate).length := by
      by_contra hge
      have : c + P'.len = (W P'.coordinate).length := by omega
      rw [this] at hcnk; omega
    rw [← (show (editedTuple W ρ N x P'.coordinate)[P'.stop]? = (W P'.coordinate)[c + P'.len]? by
      rw [show P'.stop = retainedCount (deletedPositions W ρ N x P'.coordinate)
          (c + P'.len) by omega, editedTuple,
        getElem?_deletePositions _ (hcnr hlt) hlt]),
      show c + P'.len - ρ.length = c + (P'.len - ρ.length) by omega, htext _ (by omega),
      show P'.start + (P'.len - ρ.length) = P'.stop - ρ.length by omega]
    exact h
  refine
      ⟨⟨P'.coordinate, c, c + P'.len, by omega, hcnl, hper, by rw [hroot]; exact P'.primitive,
          hmaxL,
    hmaxR⟩, ?_⟩
  apply Piece.ext_coordinates
  · rfl
  · exact hck
  · change retainedCount (deletedPositions W ρ N x P'.coordinate) (c + P'.len) = P'.stop
    rw [hcnk]; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
