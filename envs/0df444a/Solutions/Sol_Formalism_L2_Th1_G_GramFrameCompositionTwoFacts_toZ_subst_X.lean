-- Prove2me | solution 1 for Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.toZ_subst_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:24.485044+00:00
-- url     : https://prove2.me/submissions/cba1881f-37c7-444b-979a-87fad30e4a40

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_L2_Th1_G_GramFrameCompositionTwoFacts_mvSubst_subst
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
theorem _root_.solution {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : PowerSeries K) (i : n) :
    toZ linv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) f) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) (PowerSeries.subst linv f) := by
  unfold toZ
  rw [mvSubst_subst (hasSubst_zPt h0) (MvPowerSeries.constantCoeff_X i),
    MvPowerSeries.subst_X (hasSubst_zPt h0),
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]
end Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
