-- Prove2me | solution 1 for Formalism.L2.Th1.G.s2_integral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:25.955223+00:00
-- url     : https://prove2.me/submissions/4102da34-365c-476e-b0d9-ccd203e004d7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_LT_InvIntP_key


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
open GramFrameCompositionTwoFacts
namespace Formalism.L2.Th1.G
theorem _root_.solution : ShiftedSigmaConstantIntegralOfIsogenySum := by
  intro K _ _ _ s2 al albar b ι _ xP hN hu hx hb hs
  have key : al * (al - albar) * (s2 + b / 12) = ∑ P, xP P + (al ^ 2 - 1) * (b / 12) := by
    rw [mul_add, hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination (-(b / 12)) * hN
  have e : ‖s2 + b / 12‖ = ‖al * (al - albar) * (s2 + b / 12)‖ := by
    rw [norm_mul (al * (al - albar)), hu, one_mul]
  rw [e, key]
  exact (unitBall K).add_mem (Subring.sum_mem _ fun P _ => hx P) hb
end Formalism.L2.Th1.G
