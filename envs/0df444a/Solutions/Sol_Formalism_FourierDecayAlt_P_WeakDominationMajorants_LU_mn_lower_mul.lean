-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU.mn_lower_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:03:38.083882+00:00
-- url     : https://prove2.me/submissions/696496cb-9171-4465-a083-f722cfab78be

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_LU_det_updateRow_fsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_LU_split_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
theorem _root_.solution (L Y : Matrix (Fin r) (Fin r) ℂ) (hL : IsLU L) (a b : Fin r) :
    mn (L * Y) a b = ∑ t, if b ≤ t then L a t * mn Y t b else 0 := by
  classical
  set S := rs b a
  set C := cs b
  let Λ : Matrix (Fin (b.val + 1)) (Fin (b.val + 1)) ℂ := Matrix.of fun i j =>
    if j.val < b.val then L (S i) (C j) else (if i = Fin.last b.val then 1 else 0)
  let Y0 : Matrix (Fin (b.val + 1)) (Fin (b.val + 1)) ℂ := Y.submatrix C C
  let c : Fin r → ℂ := fun t => if b ≤ t then L a t else 0
  let v : Fin r → Fin (b.val + 1) → ℂ := fun t j => Y t (C j)
  let Yh := Y0.updateRow (Fin.last b.val) (∑ t, c t • v t)
  have hb : b.val ≤ r := b.isLt.le
  have key : (L * Y).submatrix S C = Λ * Yh := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [split_lt b.val hb, Fin.sum_univ_castSucc]
    have hYc : ∀ l : Fin b.val, Yh (Fin.castSucc l) j = Y (Fin.castLE hb l) (C j) := by
      intro l
      simp only [Yh, Y0]
      rw [Matrix.updateRow_ne (Fin.castSucc_lt_last l).ne]
      simp only [Matrix.submatrix_apply]
      congr 1
    have hΛc : ∀ l : Fin b.val, Λ i (Fin.castSucc l) = L (S i) (Fin.castLE hb l) := by
      intro l
      simp only [Λ, Matrix.of_apply, Fin.val_castSucc, l.isLt, if_true]
      congr 1
    simp only [hYc, hΛc]
    congr 1
    have hYl : Yh (Fin.last b.val) j = ∑ t, c t * Y t (C j) := by
      simp only [Yh, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v]
    rw [hYl]
    by_cases hi : i = Fin.last b.val
    · subst hi
      have hS : S (Fin.last b.val) = a := by
        simp only [S, rs, Fin.val_last, lt_irrefl, dite_false]
      simp only [Λ, Matrix.of_apply, Fin.val_last, lt_irrefl, if_false, if_true, one_mul, hS, c]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h1 : b.val ≤ t.val
      · have h2 : b ≤ t := Fin.le_def.2 h1
        rw [if_pos h1, if_pos h2]
      · have h2 : ¬ b ≤ t := fun h => h1 (Fin.le_def.1 h)
        rw [if_neg h1, if_neg h2, zero_mul]
    · have hilt : i.val < b.val := by
        have := i.isLt
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · exact h
        · exact absurd (Fin.ext h) hi
      simp only [Λ, Matrix.of_apply, Fin.val_last, lt_irrefl, if_false, hi, zero_mul]
      refine Finset.sum_eq_zero fun t _ => ?_
      split_ifs with h1
      · have hS : S i = ⟨i.val, by omega⟩ := by simp only [S, rs, hilt, dite_true]
        rw [hS, hL.1 _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]
      · rfl
  have hΛ : Λ.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ (fun i j h => by
      have h' : i < j := OrderDual.toDual_lt_toDual.1 h
      rw [Fin.lt_def] at h'
      simp only [Λ, Matrix.of_apply]
      split_ifs with hj hi
      · have hilt : i.val < b.val := by omega
        have hS : S i = ⟨i.val, by omega⟩ := by simp only [S, rs, hilt, dite_true]
        rw [hS]
        exact hL.1 _ _ (by rw [Fin.lt_def]; simp [C, cs]; omega)
      · exfalso; rw [hi] at h'; simp at h'; have := j.isLt; omega
      · rfl)]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [Λ, Matrix.of_apply]
    split_ifs with hi hi'
    · have hS : S i = ⟨i.val, by omega⟩ := by simp only [S, rs, hi, dite_true]
      rw [hS]; exact hL.2 _
    · rfl
    · exfalso; exact hi' (Fin.ext (by simp; have := i.isLt; omega))
  have hrow : ∀ t : Fin r, Y0.updateRow (Fin.last b.val) (v t) = Y.submatrix (rs b t) C := by
    intro t
    ext i j
    by_cases hi : i = Fin.last b.val
    · subst hi
      simp only [Matrix.updateRow_self, v, Matrix.submatrix_apply, rs, Fin.val_last, lt_irrefl, dite_false]
    · rw [Matrix.updateRow_ne hi]
      have hilt : i.val < b.val := by
        have := i.isLt
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · exact h
        · exact absurd (Fin.ext h) hi
      simp only [Y0, Matrix.submatrix_apply, rs, hilt, dite_true, C, cs]
  unfold mn
  rw [key, Matrix.det_mul, hΛ, one_mul]
  simp only [Yh]
  rw [det_updateRow_fsum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hrow t]
  by_cases h : b ≤ t
  · simp only [c, if_pos h]; rfl
  · simp only [c, if_neg h, zero_mul]
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
