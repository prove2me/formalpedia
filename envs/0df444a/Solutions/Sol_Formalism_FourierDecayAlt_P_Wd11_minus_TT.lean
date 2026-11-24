-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.minus_TT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:40.0576+00:00
-- url     : https://prove2.me/submissions/7c6098ac-cb2b-4578-a093-6a69698223b4

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_d0_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_insL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_liftMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_insert_commute_of_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_transposed_R_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_rhtUU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_Um_Uinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (b : S) (s d : K) {V Vi : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf b V) (hVi : FreeOf b Vi) (hT : FreeOf2 b T)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    d0 (ins b (lift0 (Um (A := A) (star s))) * Vi) * (Rht0 b d * T) *
        d0 (ins b (lift0 (Uinv (A := A) (star s))) * V) =
      lift0 (Um (A := A) s)ᴴ * (Rht0 b d * T) * lift0 (Um (A := A) s) := by
  set Ub : SlopeTestRemainingChoices S A := ins b (lift0 (Um (A := A) (star s))) with hUb
  set Uib : SlopeTestRemainingChoices S A := ins b (lift0 (Uinv (A := A) (star s))) with hUib
  set U0 : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s) with hU0
  set UH : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s)ᴴ with hUH
  set Rh : M2 (SlopeTestRemainingChoices S A) := Rht0 b d with hRh
  have i1 : d0 Ub * d0 Uib = 1 := by rw [← diagScalar_mul, hUb, hUib, insL_Um_Uinv, d0_one]
  have cVU : Commute (d0 V) (d0 Uib) := diagScalar_commute_diagScalar (comm_insL (cen_Uinv _) hV)
  have cVR : Commute (d0 Vi) Rh := diagScalar_commute_transposed_R_matrix hVi d
  have cU0 : Commute (d0 Ub) U0 := diagScalar_commute_liftMatrix (cen_Um s) _
  have cT : Commute (d0 Ub) T := diagScalar_insert_commute_of_free (cen_Um _) hT
  have hR : d0 Ub * Rh * UH = UH * Rh * d0 Ub := rhtUU b d s
  calc d0 (Ub * Vi) * (Rh * T) * d0 (Uib * V)
      = d0 Ub * (d0 Vi * Rh) * T * (d0 Uib * d0 V) := by
        rw [diagScalar_mul, diagScalar_mul]; simp only [mul_assoc]
    _ = d0 Ub * Rh * (d0 Vi * T * d0 V) * d0 Uib := by
        rw [cVR.eq, ← cVU.eq]; simp only [mul_assoc]
    _ = (d0 Ub * Rh * UH) * T * U0 * d0 Uib := by rw [h4]; simp only [mul_assoc]
    _ = UH * Rh * (d0 Ub * T) * U0 * d0 Uib := by rw [hR]; simp only [mul_assoc]
    _ = UH * Rh * T * (d0 Ub * U0) * d0 Uib := by rw [cT.eq]; simp only [mul_assoc]
    _ = UH * Rh * T * U0 * (d0 Ub * d0 Uib) := by rw [cU0.eq]; simp only [mul_assoc]
    _ = UH * (Rh * T) * U0 := by rw [i1, mul_one]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd11
