-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.coeff_exp_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:36:09.017478+00:00
-- url     : https://prove2.me/submissions/2a09489c-8ae4-494e-bd2b-8250496b501d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_prim
import Theorems.Thm_Formalism_L2_Th1_B_dz_prim
import Theorems.Thm_Formalism_L2_Th1_C_derivative_mvExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Universal
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.F.Universal
theorem _root_.solution (P : PowerSeries K) (n : ℕ) :
    coeff (n + 1) (B.fExp (B.sigS P) : PowerSeries K) =
      ((1 / ((n : ℚ) + 1) : ℚ) : K) * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        coeff ij.1 (-B.prim P) * coeff ij.2 (B.fExp (B.sigS P) : PowerSeries K) := by
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  have hSd : derivative K (B.sigS P) = -B.prim P := by
    rw [B.sigS, map_neg]
    exact congrArg Neg.neg (B.dz_prim _)
  have h : derivative K (B.fExp (B.sigS P) : PowerSeries K) =
      -B.prim P * (B.fExp (B.sigS P) : PowerSeries K) := by
    rw [← hSd]
    exact C.derivative_mvExp hS0
  have hc := congrArg (coeff n) h
  rw [coeff_derivative, coeff_mul] at hc
  rw [← hc]
  have hn : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
end Formalism.L2.Th1.F.Universal
