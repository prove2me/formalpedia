-- Prove2me | solution 1 for Formalism.L2.Th1.C.WeierstrassCurveSeries.subst_wTr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:15:52.558171+00:00
-- url     : https://prove2.me/submissions/1e96ce11-ee16-4c62-96aa-b7519547176a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_ChordEquation
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CurveIntegerMultiplicationSeries
import Theorems.Thm_Formalism_L2_Th1_C_WeierstrassCurveSeries_logPair
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.L2.Th1.C.WeierstrassCurveSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.C.WeierstrassCurveSeries
theorem _root_.solution (W : WeierstrassCurve K) (xP yP : K) :
    PowerSeries.subst (logSer W) (wTr W xP yP) = xPlus W xP yP + PowerSeries.C (W.b₂ / 12) := by
  have h := logPair W
  have hl : PowerSeries.HasSubst (logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' h.1
  unfold wTr
  rw [PowerSeries.subst_add hl, Pts.subst_subst h.2.2.1 h.1, h.2.2.2.1, PowerSeries.X_subst,
    PowerSeries.subst_C]
  rfl
end Formalism.L2.Th1.C.WeierstrassCurveSeries
