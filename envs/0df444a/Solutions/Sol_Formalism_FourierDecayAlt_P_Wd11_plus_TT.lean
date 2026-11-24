-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.plus_TT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:50.323023+00:00
-- url     : https://prove2.me/submissions/6b1b9228-5e46-449c-b035-34e92a52b91b

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_R_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_rhUU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_Um_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_Uinv_Um

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
theorem _root_.solution (a : S) (s D : K) {V Vi : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf a V) (hT : FreeOf2 a T)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    d0 (ins a (lift0 (Um (A := A) s)) * Vi) * (T * Rh0 a D) *
        d0 (ins a (lift0 (Uinv (A := A) s)) * V) =
      lift0 (Um (A := A) s)ᴴ * (T * Rh0 a D) * lift0 (Um (A := A) s) := by
  set Ua : SlopeTestRemainingChoices S A := ins a (lift0 (Um (A := A) s)) with hUa
  set Uia : SlopeTestRemainingChoices S A := ins a (lift0 (Uinv (A := A) s)) with hUia
  set U0 : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s) with hU0
  set UH : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s)ᴴ with hUH
  set Rh : M2 (SlopeTestRemainingChoices S A) := Rh0 a D with hRh
  have i1 : d0 Ua * d0 Uia = 1 := by rw [← diagScalar_mul, hUa, hUia, insL_Um_Uinv, d0_one]
  have i2 : d0 Uia * d0 Ua = 1 := by rw [← diagScalar_mul, hUa, hUia, insL_Uinv_Um, d0_one]
  have cVU : Commute (d0 V) (d0 Uia) := diagScalar_commute_diagScalar (comm_insL (cen_Uinv s) hV)
  have cVR : Commute (d0 V) Rh := diagScalar_commute_R_matrix hV D
  have cU0 : Commute (d0 Ua) U0 := diagScalar_commute_liftMatrix (cen_Um s) _
  have cUH : Commute (d0 Uia) UH := diagScalar_commute_liftMatrix (cen_conjTranspose (cen_Um s)) _
  have cT : Commute (d0 Uia) T := diagScalar_insert_commute_of_free (cen_Uinv s) hT
  have hR : U0 * d0 Ua * Rh = Rh * (U0 * d0 Ua) := rhUU a D s
  have e1 : Rh * (d0 Uia * d0 V) = d0 V * (Rh * d0 Uia) := by
    rw [← cVU.eq, ← mul_assoc, ← cVR.eq, mul_assoc]
  have e2 : U0 * (Rh * d0 Uia) = d0 Uia * (Rh * U0) := by
    calc U0 * (Rh * d0 Uia) = d0 Uia * (d0 Ua * U0) * Rh * d0 Uia := by
          rw [← mul_assoc (d0 Uia), i2, one_mul, mul_assoc]
      _ = d0 Uia * (U0 * d0 Ua * Rh) * d0 Uia := by rw [cU0.eq]; simp only [mul_assoc]
      _ = d0 Uia * (Rh * U0) * (d0 Ua * d0 Uia) := by rw [hR]; simp only [mul_assoc]
      _ = d0 Uia * (Rh * U0) := by rw [i1, mul_one]
  have e3 : d0 Ua * (UH * (T * d0 Uia)) = UH * T := by
    rw [← cT.eq, ← mul_assoc UH, ← cUH.eq, mul_assoc, ← mul_assoc, i1, one_mul]
  calc d0 (Ua * Vi) * (T * Rh) * d0 (Uia * V)
      = d0 Ua * ((d0 Vi * T * d0 V) * (Rh * d0 Uia)) := by
        rw [diagScalar_mul, diagScalar_mul]; simp only [mul_assoc]; rw [e1]
    _ = d0 Ua * (UH * (T * (U0 * (Rh * d0 Uia)))) := by rw [h4]; simp only [mul_assoc]
    _ = (d0 Ua * (UH * (T * d0 Uia))) * (Rh * U0) := by rw [e2]; simp only [mul_assoc]
    _ = UH * (T * Rh) * U0 := by rw [e3]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd11
