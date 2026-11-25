-- Prove2me | solution 1 for Formalism.L2.Th1.G.CurveKernelTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:16.336594+00:00
-- url     : https://prove2.me/submissions/a6ac63c2-9308-4cf8-adef-992c1303635f

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
import Theorems.Thm_Formalism_L2_Th1_C_Gram_constantCoeff_lam
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst1
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_lam
import Theorems.Thm_Formalism_L2_Th1_C_curveFrame


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
theorem _root_.solution (h : ThetaZeroJetsCurve) (hK : KernelTwo) : CurveKernelTwo := by
  intro K _ _ _ W hW s2 al albar ι _ neg xP yP hEnd hxP hyP hN hu hb hs x0 y0 hE hT hx hy n _ c hc
    G hG P hP
  obtain ⟨hlp, -, -, -, hl1⟩ := curveFrame K (unitBall K) W hW
  have hj := (h K W hW s2 al albar ι neg xP yP hEnd hxP hyP hN hu hb hs x0 y0 hE hT hx hy).2
  have cph : PowerSeries.constantCoeff (phT W x0 y0 s2) = 0 := by
    unfold phT
    rw [JetSubstitutionLemmas.cc_subst1 hlp.1, constantCoeff_lam]
  exact (hK K _ _ _ hlp hl1 cph hj n c hc G hG).2 P hP
end Formalism.L2.Th1.G
