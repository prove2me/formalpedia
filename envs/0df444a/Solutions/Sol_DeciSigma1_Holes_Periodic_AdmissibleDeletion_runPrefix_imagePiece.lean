-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_imagePiece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:45.540966+00:00
-- url     : https://prove2.me/submissions/a0a13aed-c03b-46b8-b249-b2dde68b58fb

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_runPrefix_add_mul
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_editedTuple
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_start_lt_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
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


attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start

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
variable [Fintype S] (T : Table α S k) (hN : N = Fintype.card S)
include hN
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution (P : Piece W ρ.length) {o : ℕ}
    (ho : o ≤ retainedLength (N := N) (x := x) P) :
    T.runPrefix (editedTuple W ρ N x) P.coordinate ((hx.imagePiece P).start + o) =
        T.runPrefix W P.coordinate (P.start + o) := by
  have hL := retainedLength_le (N := N) (x := x) P
  have hPl := P.start_add_len
  have hle := P.stop_le_length
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  unfold retainedLength at ho hL
  by_cases hh : o ≤ Periodic.boundaryMargin N ρ.length ∨ x P = 0
  · rw [imagePiece_start, ← hx.retainedCount_head P hh (by omega)]
    apply hx.runPrefix_editedTuple T hN P.coordinate (by omega)
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · right; left; subst h0
      exact hx.in_piece_not_mem P (by omega) P.start_lt_stop (Or.inl (by omega))
    · right; right
      exact hx.not_mem_deletedPositions_of_piece_margin P (by omega) (by omega)
        (hh.elim (fun h => Or.inl (by omega)) (fun h => Or.inr (Or.inl h)))
  · push Not at hh
    rw [imagePiece_start, ← hx.retainedCount_tail P (by omega) (by omega)]
    rw [hx.runPrefix_editedTuple T hN P.coordinate (by omega)
      (Or.inr (Or.inr (hx.in_piece_not_mem P (by omega) (by omega) (Or.inr (by omega)))))]
    have hM : Periodic.statePeriodModulus N ρ.length * x P = x P *
        (ρ.length * (Fintype.card S).factorial) := by
      rw [hN, Periodic.statePeriodModulus]; ring
    have :=
        P.runPrefix_add_mul T (o := o) (m := x P)
            (by rw [← hN]; unfold Periodic.boundaryMargin Periodic.stateTransientLength at hh;
                omega)
      (by omega)
    rw [← this, hM]
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
