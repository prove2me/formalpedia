-- Prove2me | solution 1 for Formalism.L2.Th1.C.WeierstrassCurveSeries.xIsWp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:26.054584+00:00
-- url     : https://prove2.me/submissions/f388fbaf-212f-4ae9-8a5b-45ca68da42f1

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
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_wpInU


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
theorem _root_.solution (W : WeierstrassCurve K) : XIsWp (wpReg W) (logSer W) (xS W) (W.b₂ / 12) := by
  have h := Formalism.L2.Th1.A.wpInU.{0} K W
  have hl : PowerSeries.HasSubst (logSer W) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (logPair W).1
  unfold XIsWp wpShift
  rw [map_zero, sub_zero, PowerSeries.subst_add hl, PowerSeries.subst_mul hl,
    PowerSeries.subst_pow hl, PowerSeries.subst_X hl, ← PowerSeries.coe_substAlgHom hl, map_one,
    PowerSeries.coe_substAlgHom hl, h]
  ring
end Formalism.L2.Th1.C.WeierstrassCurveSeries
