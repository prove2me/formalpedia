-- Prove2me | solution 1 for Formalism.L2.Th1.G.PairedSquareConstantCoefficients.inBlock_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:35.075834+00:00
-- url     : https://prove2.me/submissions/a62f8284-f92a-46ed-8117-a0a2fa646ca4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
import Theorems.Thm_Formalism_L2_Th1_C_mvSubst_mvExp


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.L2.Th1.G.PairedSquareConstantCoefficients
variable {K : Type} [Field K]
variable [CharZero K]
namespace Formalism.L2.Th1.G.PairedSquareConstantCoefficients
theorem _root_.solution {ι B : Type} [Finite ι] (k : B) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : inBlock k (mvExp f) = mvExp (inBlock k f) := by
  unfold inBlock
  exact mvSubst_mvExp hf
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _)
end Formalism.L2.Th1.G.PairedSquareConstantCoefficients
