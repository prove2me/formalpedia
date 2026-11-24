-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.isU_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:40.50798+00:00
-- url     : https://prove2.me/submissions/7f2443ac-702c-41a9-884a-9d9dbdfe4069

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_const
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_mul
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_pOf
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul


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
namespace Formalism.L2.Th1.F.Universal
theorem _root_.solution (n : ℕ) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => coeff n (-B.prim (pOf g2 g3))) := by
  by_cases hn : n = 0
  · exact (isU_const 0).congr fun K _ _ g2 g3 => by
      rw [map_neg, B.prim, coeff_mk, if_pos hn]; simp
  · refine ((isU_pOf (n - 1)).mul (isU_const (-1 / (n : ℚ)))).congr fun K _ _ g2 g3 => ?_
    rw [map_neg, B.prim, coeff_mk, if_neg hn]
    push_cast
    ring
end Formalism.L2.Th1.F.Universal
