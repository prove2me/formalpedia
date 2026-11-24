-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaUniversal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:59.292772+00:00
-- url     : https://prove2.me/submissions/81581475-ef4a-4a13-a7c5-0e7f98515e73

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_sigma

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
namespace Formalism.L2.Th1.F
theorem _root_.solution (hu : IsWpUnique) (hp : POfIsWp) : SigmaUniversal := by
  choose U hU using Universal.isU_sigma
  refine ⟨U, fun K _ _ g2 g3 P hP n => ?_⟩
  rw [hu K g2 g3 P (pOf g2 g3) hP (hp K g2 g3)]
  exact hU n K g2 g3
end Formalism.L2.Th1.F
