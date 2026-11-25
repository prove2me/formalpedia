-- Prove2me | solution 1 for Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.jetsIn_phSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:48:27.062395+00:00
-- url     : https://prove2.me/submissions/e9123823-f223-4460-885e-a75ddb56c609

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_C
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_X
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_mul
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_subst_one
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_sum


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
theorem _root_.solution [CharZero K] {R : Subring K} {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ i, c i ∈ R) {f : PowerSeries K} (hf : JetsIn1 R f) :
    JetsIn R (phSum c f) := by
  unfold phSum
  refine jetsIn_sum _ _ fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul]
  exact jetsIn_mul (jetsIn_C (hc i))
    (jetsIn_subst_one hf (MvPowerSeries.constantCoeff_X i) (jetsIn_X i))
end Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
