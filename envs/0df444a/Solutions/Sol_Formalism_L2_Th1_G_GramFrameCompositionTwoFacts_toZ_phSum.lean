-- Prove2me | solution 1 for Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.toZ_phSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:42.406963+00:00
-- url     : https://prove2.me/submissions/295b8efc-a374-4769-899e-d300ebdd8710

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_L2_Th1_G_GramFrameCompositionTwoFacts_toZHom_apply
import Theorems.Thm_Formalism_L2_Th1_G_GramFrameCompositionTwoFacts_toZ_subst_X
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst


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
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
open Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
theorem _root_.solution {n : Type} [Fintype n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (c : n → K) (ph : PowerSeries K) :
    toZ linv (phSum c ph) = phSum c (PowerSeries.subst linv ph) := by
  unfold phSum
  rw [← toZHom_apply h0, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, toZHom_apply, toZ_subst_X h0]
end Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
