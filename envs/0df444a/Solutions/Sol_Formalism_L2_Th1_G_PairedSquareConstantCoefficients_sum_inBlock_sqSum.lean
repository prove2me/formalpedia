-- Prove2me | solution 1 for Formalism.L2.Th1.G.PairedSquareConstantCoefficients.sum_inBlock_sqSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:12.286209+00:00
-- url     : https://prove2.me/submissions/57d89b6f-4695-4633-af06-944b42f7517e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_inBlock_eq_rename


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
namespace Formalism.L2.Th1.G.PairedSquareConstantCoefficients
theorem _root_.solution {ι B : Type} [Fintype ι] [Fintype B] (s : K) (c : ι → K) :
    ∑ k : B, inBlock k (MvPowerSeries.C s * sqSum c) =
      MvPowerSeries.C s * sqSum (fun a : B × ι => c a.2) := by
  simp [HurwitzJetIntegrality.inBlock_eq_rename, sqSum, Finset.mul_sum, Fintype.sum_prod_type]
  rfl
end Formalism.L2.Th1.G.PairedSquareConstantCoefficients
