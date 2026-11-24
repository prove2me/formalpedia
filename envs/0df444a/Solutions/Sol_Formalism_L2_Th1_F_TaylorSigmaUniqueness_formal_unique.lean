-- Prove2me | solution 1 for Formalism.L2.Th1.F.TaylorSigmaUniqueness.formal_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:47.061237+00:00
-- url     : https://prove2.me/submissions/6bac2bee-9d57-43c3-99d7-683cc25b2b6e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_prim
import Theorems.Thm_Formalism_L2_Th1_B_dz_prim
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_derivative_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.TaylorSigmaUniqueness
open PowerSeries
namespace Formalism.L2.Th1.F.TaylorSigmaUniqueness
theorem _root_.solution (P U V : PowerSeries ℂ) (hV : X * derivative ℂ V = -(X * P))
    (hV0 : constantCoeff V = 0) (hU : X * derivative ℂ U = X * (V * U))
    (hU0 : constantCoeff U = 1) : U = B.fExp (B.sigS P) := by
  have hV' : derivative ℂ V = -P := by
    apply mul_left_cancel₀ (X_ne_zero (R := ℂ))
    rw [hV, mul_neg]
  have hU' : derivative ℂ U = V * U := mul_left_cancel₀ (X_ne_zero (R := ℂ)) hU
  have hVp : V = -B.prim P := by
    refine derivative.ext ?_ ?_
    · rw [hV', map_neg]
      exact congrArg Neg.neg (B.dz_prim P).symm
    · rw [hV0, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0' : constantCoeff (-B.sigS P) = 0 := by rw [map_neg, hS0, neg_zero]
  have hSd : derivative ℂ (B.sigS P) = V := by
    rw [B.sigS, map_neg, hVp]
    exact congrArg Neg.neg (B.dz_prim _)
  have key : U * (C.mvExp (-B.sigS P) : PowerSeries ℂ) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, C.derivative_mvExp hS0', map_neg, hSd, hU', Derivation.map_one_eq_zero]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, hU0, map_one, one_mul]
      exact C.constantCoeff_mvExp hS0'
  have h2 : (C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P) = 1 := C.mvExp_neg hS0
  calc U = U * ((C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P)) := by rw [h2, mul_one]
    _ = C.mvExp (B.sigS P) := by rw [← mul_assoc, key, one_mul]
    _ = B.fExp (B.sigS P) := rfl
end Formalism.L2.Th1.F.TaylorSigmaUniqueness
