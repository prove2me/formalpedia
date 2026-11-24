-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.isU_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:39.839913+00:00
-- url     : https://prove2.me/submissions/0ab4856f-1473-4ab1-b109-4843db23e103

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_const
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_exp

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
theorem _root_.solution (n : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 =>
    coeff n (B.sigma (pOf g2 g3))) := by
  rcases n with _ | n
  · exact (isU_const 0).congr fun K _ _ g2 g3 => by
      rw [B.sigma, coeff_zero_X_mul]; simp
  · exact (isU_exp n).congr fun K _ _ g2 g3 => by
      rw [B.sigma, coeff_succ_X_mul]
end Formalism.L2.Th1.F.Universal
