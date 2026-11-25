-- Prove2me | solution 1 for Formalism.L2.Th1.C.curve_formal_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:58:28.669165+00:00
-- url     : https://prove2.me/submissions/62055389-2e97-4e59-8292-7cbd70aa0d8a

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
import Theorems.Thm_Formalism_L2_Th1_C_WeierstrassCurveSeries_xIsWp
import Theorems.Thm_Formalism_L2_Th1_A_coeffMem
import Theorems.Thm_Formalism_L2_Th1_A_fglLog
import Theorems.Thm_Formalism_L2_Th1_A_logSpec
import Theorems.Thm_Formalism_L2_Th1_A_unitSpec
import Theorems.Thm_Formalism_L2_Th1_A_wSerFactor


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
open WeierstrassCurveSeries
namespace Formalism.L2.Th1.C
theorem _root_.solution : CurveFrame := by
  intro K _ _ R W hW
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨-, hx, -, -, hom, -, hF, -⟩ := Formalism.L2.Th1.A.coeffMem.{0} K W R h1 h2 h3 h4 h6
  refine ⟨logPair W, xIsWp W, ⟨(Formalism.L2.Th1.A.wSerFactor.{0} K W).2.2.2.1, hx⟩, ?_, ?_⟩
  · intro n
    have := (Formalism.L2.Th1.A.fglLog.{0} K W).2
    unfold fadd
    rw [← this]
    exact hF n
  · rw [(Formalism.L2.Th1.A.logSpec.{0} K W).2.2.1]
    exact ⟨(Formalism.L2.Th1.A.unitSpec.{0} K W).2.2.1, hom⟩
end Formalism.L2.Th1.C
