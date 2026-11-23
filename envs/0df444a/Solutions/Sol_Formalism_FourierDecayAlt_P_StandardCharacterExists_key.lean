-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:15.622946+00:00
-- url     : https://prove2.me/submissions/82221fe3-bbf2-4949-8ec3-26257bbf2d45

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_X_eq_ex
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_B_eq_ex
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_x_eq_ex__214907

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution (m : ℕ) (z : ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ)
    (hX : IsStrictUpper X) (hx : ∀ k, xOf X B k = z) (j : ℕ) :
    (∀ i : Fin (m + 1), m < (i : ℕ) + j → ((-X) ^ j *ᵥ B) i = 0) ∧
    (∀ i : Fin (m + 1), (i : ℕ) + j = m → ((-X) ^ j *ᵥ B) i = (-z) ^ j * z) ∧
    (∀ i : Fin (m + 1), (i : ℕ) + j + 1 = m →
      ((-X) ^ j *ᵥ B) i = (-z) ^ j * ∑ k ∈ Finset.Ico (i : ℕ) m, ex (blk X B 0 0) k (k + 2)) := by
  induction j with
  | zero =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · have := i.isLt; omega
    · have h := hx i
      rw [x_eq_ex] at h
      simp only [pow_zero, Matrix.one_mulVec, one_mul]
      rw [B_eq_ex X B i, ← h]
      congr 1; omega
    · simp only [pow_zero, Matrix.one_mulVec, one_mul]
      have hI : Finset.Ico (i : ℕ) m = {(i : ℕ)} := by
        ext a; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      rw [hI, Finset.sum_singleton, B_eq_ex X B i]
      congr 1; omega
  | succ j ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    have hstep : ∀ i : Fin (m + 1), ((-X) ^ (j + 1) *ᵥ B) i = ∑ k, -(X i k * ((-X) ^ j *ᵥ B) k) := by
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      simp [Matrix.mulVec, dotProduct]
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [hstep]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k ≤ i
      · rw [hX i k hk]; simp
      · have hk' : (i : ℕ) < k := by simpa using hk
        rw [ih0 k (by omega)]; simp
    · rw [hstep]
      have hlt : (i : ℕ) + 1 < m + 1 := by omega
      rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hlt⟩ : Fin (m + 1))]
      · rw [ih1 _ (by simp only; omega)]
        have h := hx i
        rw [x_eq_ex] at h
        rw [X_eq_ex X B]
        simp only
        rw [h]; ring
      · intro k _ hk
        by_cases hk1 : k ≤ i
        · rw [hX i k hk1]; simp
        · have hk' : (i : ℕ) < k := by simpa using hk1
          have hk2 : (k : ℕ) ≠ (i : ℕ) + 1 := fun h => hk (Fin.ext h)
          rw [ih0 k (by omega)]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [hstep]
      have hlt : (i : ℕ) + 1 < m + 1 := by omega
      have hlt2 : (i : ℕ) + 2 < m + 1 := by omega
      rw [Finset.sum_eq_add (⟨(i : ℕ) + 1, hlt⟩ : Fin (m + 1)) (⟨(i : ℕ) + 2, hlt2⟩ : Fin (m + 1))]
      · rw [ih2 _ (by simp only; omega), ih1 _ (by simp only; omega)]
        have h := hx i
        rw [x_eq_ex] at h
        rw [X_eq_ex X B, X_eq_ex X B]
        simp only
        rw [h, Finset.sum_eq_sum_Ico_succ_bot (show (i : ℕ) < m by omega)]
        ring
      · intro h
        have := congrArg Fin.val h
        simp at this
      · intro k _ hk
        by_cases hk1 : k ≤ i
        · rw [hX i k hk1]; simp
        · have hk' : (i : ℕ) < k := by simpa using hk1
          have hk2 : (k : ℕ) ≠ (i : ℕ) + 1 := fun h => hk.1 (Fin.ext h)
          have hk3 : (k : ℕ) ≠ (i : ℕ) + 2 := fun h => hk.2 (Fin.ext h)
          rw [ih0 k (by omega)]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.StandardCharacterExists
