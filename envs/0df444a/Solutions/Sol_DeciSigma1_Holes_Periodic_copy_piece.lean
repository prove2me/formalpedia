-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.copy_piece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:12.650503+00:00
-- url     : https://prove2.me/submissions/a87020e0-401c-426f-b52d-0e416a72decd

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
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_root_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_exists_piece_of_stretch
public import Theorems.Thm_DeciSigma1_Holes_Periodic_piece_eq_of_overlap
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
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
variable [DecidableEq α] {V : Fin k → List α} {d : ℕ}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {a b : Fin k} {u v m : ℕ}
    (hag : ∀ n < m, (V a)[u + n]? = (V b)[v + n]?) (R : Piece V d) (hRl : R.coordinate = a)
    (h1 : u < R.start) {ℓ : ℕ} (hℓ : 2 * d ≤ ℓ) (hℓR : R.start + ℓ ≤ R.stop)
        (hℓm : R.start + ℓ ≤ u + m) :
    ∃ P : Piece V d, P.coordinate = b ∧ P.start = v + (R.start - u) ∧ P.root = R.root ∧
      v + (R.start - u) + ℓ ≤ P.stop ∧
      (R.stop < u + m → R.stop < (V a).length → P.stop = v + (R.stop - u)) := by
  subst hRl
  have hd := R.period_pos
  have hle := R.stop_le_length
  -- letters of `R` up to `R.start + ℓ` exist on the other side
  have hcopy : ∀ p, u ≤ p → p < u + m → (V R.coordinate)[p]? = (V b)[v + (p - u)]? := by
    intro p hp hpm; have := hag (p - u) (by omega); rwa [Nat.add_sub_cancel' hp] at this
  have hlen : v + (R.start - u) + ℓ ≤ (V b).length := by
    have h := hcopy (R.start + ℓ - 1) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at h
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  have hper : PeriodicOn (V b) d (v + (R.start - u)) (v + (R.start - u) + ℓ) := by
    intro p hp hpe
    have e1 := hcopy (p - v + u) (by omega) (by omega)
    have e2 := hcopy (p - v + u + d) (by omega) (by omega)
    rw [show v + (p - v + u - u) = p by omega] at e1
    rw [show v + (p - v + u + d - u) = p + d by omega] at e2
    rw [← e1, ← e2]
    exact R.periodic _ (by omega) (by omega)
  have hwin : ((V b).drop (v + (R.start - u))).take d = R.root := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < d
    · rw [List.getElem?_take_of_lt ht, List.getElem?_drop, Piece.root, List.getElem?_take_of_lt ht,
        List.getElem?_drop, hcopy (R.start + t) (by omega) (by omega)]
      congr 1; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
        (by rw [R.root_length]; omega)]
  have hbrkL : v + (R.start - u) = 0 ∨ (V b)[v + (R.start - u) - 1]? ≠
      (V b)[v + (R.start - u) - 1 + d]? := by
    right
    rcases R.left_maximal with h | h
    · omega
    · have e1 := hcopy (R.start - 1) (by omega) (by omega)
      have e2 := hcopy (R.start - 1 + d) (by omega) (by omega)
      rw [show v + (R.start - 1 - u) = v + (R.start - u) - 1 by omega] at e1
      rw [show v + (R.start - 1 + d - u) = v + (R.start - u) - 1 + d by omega] at e2
      rw [← e1, ← e2]; exact h
  obtain ⟨P, hPl, hPs, hPe, hcls, hL, hR⟩ := exists_piece_of_stretch V b (by omega) hlen hper
    (by rw [hwin]; exact R.primitive)
  have hPs' : P.start = v + (R.start - u) := hL hbrkL
  refine ⟨P, hPl, hPs', ?_, hPe, ?_⟩
  · change ((V P.coordinate).drop P.start).take d = R.root
    rw [hPl, hPs']; exact hwin
  · intro hRm hRlen
    -- the right break of `R` is copied
    have hEle : R.start + ℓ ≤ R.stop := hℓR
    rcases R.right_maximal with h | h
    · omega
    · have hstretch : PeriodicOn (V b) d (v + (R.start - u)) (v + (R.stop - u)) := by
        intro p hp hpe
        have e1 := hcopy (p - v + u) (by omega) (by omega)
        have e2 := hcopy (p - v + u + d) (by omega) (by omega)
        rw [show v + (p - v + u - u) = p by omega] at e1
        rw [show v + (p - v + u + d - u) = p + d by omega] at e2
        rw [← e1, ← e2]
        exact R.periodic _ (by omega) (by omega)
      have hlen' : v + (R.stop - u) ≤ (V b).length := by
        have h' := hcopy R.stop (by omega) hRm
        rw [List.getElem?_eq_getElem hRlen] at h'
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at h'
        exact absurd h' (by simp)
      obtain ⟨P₂, hP₂l, hP₂s, hP₂e, _, hL₂, hR₂⟩ := exists_piece_of_stretch V b (by omega) hlen'
        hstretch (by rw [hwin]; exact R.primitive)
      have hP₂s' := hL₂ hbrkL
      have hP₂e' : P₂.stop = v + (R.stop - u) := hR₂ (by
        right
        have e1 := hcopy R.stop (by omega) hRm
        have e2 := hcopy (R.stop - d) (by omega) (by omega)
        rw [show v + (R.stop - d - u) = v + (R.stop - u) - d by omega] at e2
        rw [← e1, ← e2]; exact h)
      have : P = P₂ := Piece.ext_coordinates (hPl.trans hP₂l.symm) (hPs'.trans hP₂s'.symm) (by
        by_contra hne
        exact absurd (piece_eq_of_overlap (P := P) (Q := P₂) (hPl.trans hP₂l.symm)
          (by omega) (by omega)) (by intro h'; rw [h'] at hne; exact hne rfl))
      rw [this, hP₂e']
end DeciSigma1.Holes.Periodic
