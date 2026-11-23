-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_redOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:09.892807+00:00
-- url     : https://prove2.me/submissions/d858c2ad-a1f7-4f75-adf0-1c5fb1c8783a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_succ_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_succ_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_zero_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_zero_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_diagonal_cons_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
theorem _root_.solution (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by
  ext i j
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun i => ?_) i
  · have hs : subShift (m + 2) 0 j = 0 := by simp [subShift]
    rw [hs, mul_zero, zero_add]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [wM_zero_last]
      simp [redOf, triXY]
    · rw [wM_zero_cast]
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [strictUpper]
      · have h : (0 : Fin (m + 2)) ≠ k.castSucc.succ := (Fin.succ_ne_zero _).symm
        simp [redOf, triXY, Matrix.diagonal_apply_ne _ h]
  · rw [diagonal_cons_succ ρ₁ 0]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [wM_succ_last]
      have hs : subShift (m + 2) i.succ (Fin.last (m + 1)) = 0 := by
        have := i.isLt
        simp only [subShift, Matrix.of_apply, Fin.val_last, Fin.val_succ]
        rw [if_neg (by omega)]
      rw [hs, mul_zero, zero_add]
      simp [redOf, triXY]
    · rw [wM_succ_cast]
      have hs : subShift (m + 2) i.succ j.castSucc = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i j := by
        simp only [subShift, Matrix.of_apply, Fin.val_castSucc, Fin.val_succ, Matrix.one_apply, Fin.ext_iff]
        by_cases h : (i : ℕ) = j
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [hs, add_assoc]
      congr 1
      by_cases h : i < j
      · simp [redOf, triXY, strictUpper, h]
      · have h1 : i.succ ≠ j.castSucc := by
          intro e
          have := congrArg Fin.val e
          simp only [Fin.val_succ, Fin.val_castSucc] at this
          exact h (by rw [Fin.lt_def]; omega)
        have h2 : ¬ (i.succ < j.castSucc) := by
          intro e
          rw [Fin.lt_def] at e
          simp only [Fin.val_succ, Fin.val_castSucc] at e
          exact h (by rw [Fin.lt_def]; omega)
        simp [strictUpper, h, h2, Matrix.diagonal_apply_ne _ h1]
end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
