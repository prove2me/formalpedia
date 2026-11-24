-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.isU_pOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:40.647857+00:00
-- url     : https://prove2.me/submissions/e4e2d635-20e7-4a6f-b161-8c5528c80d14

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_const
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_cW
import Theorems.Thm_Formalism_L2_Th1_F_POf_coeff_pOf


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
theorem _root_.solution (n : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 => coeff n (pOf g2 g3)) := by
  by_cases hn : Even n
  · exact (isU_cW (n / 2 + 1)).congr fun K _ _ g2 g3 => by rw [POf.coeff_pOf, if_pos hn]
  · exact (isU_const 0).congr fun K _ _ g2 g3 => by rw [POf.coeff_pOf, if_neg hn]; simp
end Formalism.L2.Th1.F.Universal
