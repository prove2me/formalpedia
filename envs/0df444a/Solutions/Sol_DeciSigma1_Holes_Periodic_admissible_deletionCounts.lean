-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.admissible_deletionCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:35.458018+00:00
-- url     : https://prove2.me/submissions/14073656-60ca-4fc1-9a0b-d6fcc6891ce2

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_floor_edit
public import Theorems.Thm_DeciSigma1_Holes_Periodic_far_weight
public import Theorems.Thm_DeciSigma1_Holes_Periodic_deletionCounts_val
public import Theorems.Thm_DeciSigma1_Holes_Periodic_retained_cast
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
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
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
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



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (hs : (shiftSystem W ρ N).Sat z)
    (hf : ∀ P, shiftFloor N P.val ≤ z P) (hz0 : ∀ P, z P ≤ 0)
    (hM : 0 < statePeriodModulus N ρ.length) : AdmissibleDeletion W ρ N (deletionCounts z) where
  supp := by
    intro P hp
    by_contra hnot
    simp [deletionCounts, hnot] at hp
  long := by
    intro P hP hmove
    rw [deletionCounts_val (⟨P, hP⟩ : {P // P ∈ piecesOf W ρ})] at hmove ⊢
    exact (floor_edit (hf ⟨P, hP⟩) (hz0 ⟨P, hP⟩)).2.2 hmove
  near := by
    intro P hP Q hQ hg hPQ hQP
    have h1 := hs ⟨P, hP⟩ ⟨Q, hQ⟩ 0 (by simp [shiftSystem, hg, hPQ, hQP])
    have h2 := hs ⟨Q, hQ⟩ ⟨P, hP⟩ 0 (by simp [shiftSystem, hg.symm, hPQ, hQP])
    have he : z ⟨P, hP⟩ = z ⟨Q, hQ⟩ := by omega
    simp only [deletionCounts, dif_pos hP, dif_pos hQ, he]
  far := by
    intro P hP Q hQ hg hfar
    have hnot : ¬
        (P.len < Q.len + comparisonGap N ρ.length ∧ Q.len < P.len + comparisonGap N
            ρ.length) := by omega
    have he := hs ⟨P, hP⟩ ⟨Q, hQ⟩
      (-(((Q.len - P.len - comparisonGap N ρ.length) / statePeriodModulus N ρ.length : ℕ) : ℤ))
      (by simp [shiftSystem, hg, hnot, hfar])
    have hw := far_weight hM hfar (by simpa only [sub_eq_add_neg] using he)
    have hp := retained_cast hf hz0 ⟨P, hP⟩
    have hq := retained_cast hf hz0 ⟨Q, hQ⟩
    dsimp only at hp hq hw
    omega
end DeciSigma1.Holes.Periodic
