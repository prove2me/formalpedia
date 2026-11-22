-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.copy_stretch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:46.6813+00:00
-- url     : https://prove2.me/submissions/c9e34482-0207-47f3-b04a-5d7c045259e1

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
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_window_isConjugate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_exists_piece_of_stretch
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_isPrimitive
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
    (h1 : R.start ≤ u) {ℓ : ℕ} (hℓ : 2 * d < ℓ) (hℓR : u + ℓ ≤ R.stop) (hℓm : ℓ ≤ m) :
    ∃ P : Piece V d, P.coordinate = b ∧ P.start ≤ v ∧ v + ℓ ≤ P.stop ∧ IsConjugate P.root R.root ∧
      (u + ℓ = R.stop → ℓ < m → R.stop < (V a).length → P.stop = v + ℓ) := by
  subst hRl
  have hd := R.period_pos
  have hle := R.stop_le_length
  have hcopy : ∀ p, u ≤ p → p < u + m → (V R.coordinate)[p]? = (V b)[v + (p - u)]? := by
    intro p hp hpm; have := hag (p - u) (by omega); rwa [Nat.add_sub_cancel' hp] at this
  have hlen : v + ℓ ≤ (V b).length := by
    have h := hcopy (u + ℓ - 1) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at h
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  have hper : PeriodicOn (V b) d v (v + ℓ) := by
    intro p hp hpe
    have e1 := hcopy (p - v + u) (by omega) (by omega)
    have e2 := hcopy (p - v + u + d) (by omega) (by omega)
    rw [show v + (p - v + u - u) = p by omega] at e1
    rw [show v + (p - v + u + d - u) = p + d by omega] at e2
    rw [← e1, ← e2]
    exact R.periodic _ (by omega) (by omega)
  have hwin : ((V b).drop v).take d = ((V R.coordinate).drop u).take d := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < d
    · rw [List.getElem?_take_of_lt ht, List.getElem?_drop, List.getElem?_take_of_lt ht,
        List.getElem?_drop, hcopy (u + t) (by omega) (by omega)]
      congr 1; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hRcls : IsConjugate R.root (((V R.coordinate).drop u).take d) :=
      R.window_isConjugate h1 (by omega)
  obtain ⟨P, hPl, hPs, hPe, hcls, _, hR⟩ := exists_piece_of_stretch V b (by omega) hlen hper
    (by rw [hwin]; exact hRcls.isPrimitive R.primitive)
  refine ⟨P, hPl, hPs, hPe, ?_, ?_⟩
  · rw [hwin] at hcls; exact hcls.trans hRcls.symm
  · intro hend hlm hRlen
    apply hR
    right
    rcases R.right_maximal with h | h
    · omega
    · have e1 := hcopy R.stop (by omega) (by omega)
      have e2 := hcopy (R.stop - d) (by omega) (by omega)
      rw [show v + (R.stop - u) = v + ℓ by omega] at e1
      rw [show v + (R.stop - d - u) = v + ℓ - d by omega] at e2
      rw [← e1, ← e2]; exact h
end DeciSigma1.Holes.Periodic
