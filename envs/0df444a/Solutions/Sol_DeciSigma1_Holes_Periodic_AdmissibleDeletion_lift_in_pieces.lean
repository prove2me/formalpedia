-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.lift_in_pieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:35.335728+00:00
-- url     : https://prove2.me/submissions/84b633d4-92eb-4639-81f0-3e089e61dde6

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_piece_suffixComparison
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_mod_d_of_mod_statePeriodModulus
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop_eq
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_imagePiece
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_runPrefix_mod
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
public import Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_AdmissibleDeletion_getElem__imagePiece_5b6104921581
public import Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_Piece_getElem__eq_of_mod_eddd45ef4561
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
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
theorem _root_.solution {S : Type} [Fintype S] (T : Table α S k) (hNS : N = Fintype.card S)
    {i j : Fin k} {P Q : Piece W ρ.length} (hPl : P.coordinate = j) (hQl : Q.coordinate = i)
    {b' a' pT pS oT oS : ℕ} (hb' : b' = (hx.imagePiece P).start + pT)
        (ha' : a' = (hx.imagePiece Q).start + pS)
    (hpT : pT + ρ.length ≤ retainedLength (N := N) (x := x) P)
    (hpS : pS + ρ.length ≤ retainedLength (N := N) (x := x) Q) (hoT : oT ≤ P.len) (hoS : oS ≤ Q.len)
    (hT : SameStatePhase N ρ.length oT pT) (hS : SameStatePhase N ρ.length oS pS)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a')
    (hlen : P.len - oT ≤ Q.len - oS)
    (hfol : P.stop = (W j).length ∨ (P.len - oT = Q.len - oS ∧ SuffixComparison (W j) P.stop
        (W i) Q.stop)) :
    SuffixComparison (W j) (P.start + oT) (W i) (Q.start + oS) ∧ T.runPrefix W j (P.start + oT) =
        T.runPrefix (editedTuple W ρ N x) j b' ∧
      T.runPrefix W i (Q.start + oS) = T.runPrefix (editedTuple W ρ N x) i a' := by
  have hLP := retainedLength_le (N := N) (x := x) P
  have hLQ := retainedLength_le (N := N) (x := x) Q
  have hd := P.period_pos
  have hmT := mod_d_of_mod_statePeriodModulus hT
  have hmS := mod_d_of_mod_statePeriodModulus hS
  have hPe : (hx.imagePiece P).stop ≤ (editedTuple W ρ N x j).length := by
    have := (hx.imagePiece P).stop_le_length; rw [imagePiece_coordinate, hPl] at this; exact this
  have hPimg := hx.imagePiece_stop_eq P
  -- states
  have hstate : ∀ (R : Piece W ρ.length) (o p : ℕ) (l : Fin k), R.coordinate = l → o ≤ R.len →
      p ≤ retainedLength (N := N) (x := x) R → SameStatePhase N ρ.length o p →
      T.runPrefix W l (R.start + o) =
          T.runPrefix (editedTuple W ρ N x) l ((hx.imagePiece R).start + p) := by
    intro R o p l hRl ho hp h
    subst hRl
    rw [hx.runPrefix_imagePiece T hNS R hp]
    rcases h with h | ⟨h1, h2, h3⟩
    · rw [h]
    · have := retainedLength_le (N := N) (x := x) R
      subst hNS
      exact R.runPrefix_mod T h1 h2 ho (by omega) h3
  refine ⟨?_, by rw [hb']; exact hstate P oT pT j hPl hoT (by omega) hT,
    by rw [ha']; exact hstate Q oS pS i hQl hoS (by omega) hS⟩
  have hanchor : ∀ t < ρ.length, t < P.len - oT →
      (W P.coordinate)[P.start + oT + t]? = (W Q.coordinate)[Q.start + oS + t]? := by
    intro t ht ht'
    have e1 := P.getElem?_eq_of_mod (o₁ := oT + t) (o₂ := pT + t) (by omega) (by omega)
      (by rw [Nat.add_mod, hmT, ← Nat.add_mod])
    have e2 := hx.getElem?_imagePiece P (o := pT + t) (by omega)
    have e3 := hx.getElem?_imagePiece Q (o := pS + t) (by omega)
    have e4 := Q.getElem?_eq_of_mod (o₁ := pS + t) (o₂ := oS + t) (by omega) (by omega)
      (by rw [Nat.add_mod, ← hmS, ← Nat.add_mod])
    have e5 := hcmp t (by rw [hb']; omega)
    simp only [Nat.add_assoc] at e1 e2 e3 e4 ⊢
    rw [e1, ← e2, hPl, ← Nat.add_assoc, ← hb', e5, ha', ← hQl, Nat.add_assoc, e3, e4]
  have := piece_suffixComparison P Q hoT hoS hanchor hlen (by rw [hPl, hQl]; exact hfol)
  rwa [hPl, hQl] at this
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
