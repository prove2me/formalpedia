-- Prove2me | solution 1 for Formalism.L2.Th1.F.POf.pOf_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:52:00.277995+00:00
-- url     : https://prove2.me/submissions/9ad42385-1f68-45fc-af19-69468f2de35e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Theorems.Thm_Formalism_L2_Th1_F_POf_cW_one
import Theorems.Thm_Formalism_L2_Th1_F_POf_cW_two
import Theorems.Thm_Formalism_L2_Th1_F_POf_cW_three
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
open Formalism.L2.Th1.CM (cW wpNum wpDen)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F Formalism.L2.Th1.F.POf
variable {K : Type} [Field K]
variable [CharZero K]
namespace Formalism.L2.Th1.F.POf
theorem _root_.solution (g2 g3 : K) :
    pOf g2 g3 = C (g2 / 20) * X ^ 2 + C (g3 / 28) * X ^ 4
      + X ^ 6 * PowerSeries.mk fun n => coeff (n + 6) (pOf g2 g3) := by
  ext n
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp [coeff_pOf, cW_one]
  · simp [coeff_pOf]
  · simp [coeff_pOf, cW_two]
  · simp [coeff_pOf]; exact fun h => absurd h (by decide)
  · simp [coeff_pOf, cW_three]; exact fun h => absurd h (by decide)
  · simp [coeff_pOf]; exact fun h => absurd h (by decide)
  · simp
end Formalism.L2.Th1.F.POf
