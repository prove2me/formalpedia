-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.piece_suffixComparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:23.199724+00:00
-- url     : https://prove2.me/submissions/71fb4b56-0103-4387-8b18-723cf2181437

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
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
variable [DecidableEq α] {W : Fin k → List α} {d : ℕ}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (P Q : Piece W d) {oP oQ : ℕ} (hoP : oP ≤ P.len) (hoQ : oQ ≤ Q.len)
    (hanchor : ∀ t < d,
        t < P.len - oP → (W P.coordinate)[P.start + oP + t]? = (W Q.coordinate)[Q.start + oQ + t]?)
    (hlen : P.len - oP ≤ Q.len - oQ)
    (hfol : P.stop = (W P.coordinate).length ∨ (P.len - oP = Q.len - oQ ∧ SuffixComparison
        (W P.coordinate) P.stop (W Q.coordinate) Q.stop)) :
    SuffixComparison (W P.coordinate) (P.start + oP) (W Q.coordinate) (Q.start + oQ) := by
  classical
  have hd := P.period_pos
  have hPl := P.start_add_len
  have hQl := Q.start_add_len
  intro n hn
  rcases Nat.lt_or_ge n (P.len - oP) with h | h
  · have hmle := Nat.mod_le n d
    have e1 := P.getElem?_eq_of_mod (o₁ := oP + n) (o₂ := oP + n % d) (by omega) (by omega)
      (Nat.add_mod_mod oP n d).symm
    have e2 := hanchor (n % d) (Nat.mod_lt _ hd) (by omega)
    have e3 := Q.getElem?_eq_of_mod (o₁ := oQ + n % d) (o₂ := oQ + n) (by omega) (by omega)
      (Nat.add_mod_mod oQ n d)
    simp only [Nat.add_assoc] at e1 e2 e3 ⊢
    rw [e1, e2, e3]
  · rcases hfol with hE | ⟨heq, hcmp⟩
    · omega
    · have := hcmp (n - (P.len - oP)) (by omega)
      rwa [show P.stop + (n - (P.len - oP)) = P.start + oP + n by omega,
        show Q.stop + (n - (P.len - oP)) = Q.start + oQ + n by omega] at this
end DeciSigma1.Holes.Periodic
