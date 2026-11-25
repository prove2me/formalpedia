-- Prove2me | solution 1 for Formalism.L2.Th1.G.Th0JetsCurve_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:55.08742+00:00
-- url     : https://prove2.me/submissions/97038da3-8309-4074-8196-7b7f1674920d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_neg
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs


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
theorem _root_.solution (h1 : ShiftedSigmaConstantIntegralOfIsogenySum) (h2 : ThetaZeroJetsTwo) : ThetaZeroJetsCurve := by
  intro K _ _ _ W hW s2 al albar ι _ neg xP yP _ hxP _ hN hu hb hs x0 y0 hE hT hx hy
  have a1 : ‖s2 + W.b₂ / 12‖ ≤ 1 := h1 K s2 al albar W.b₂ ι xP hN hu hxP hb hs
  have a2 : ‖x0 + W.b₂ / 12 + s2‖ ≤ 1 := by
    have e : x0 + W.b₂ / 12 + s2 = x0 + (s2 + W.b₂ / 12) := by ring
    rw [e]
    exact (unitBall K).add_mem hx a1
  obtain ⟨q1, q2, -⟩ := h2 K W hW x0 y0 s2 hE hT hx hy a2
  exact ⟨q2, q1⟩
end Formalism.L2.Th1.G
