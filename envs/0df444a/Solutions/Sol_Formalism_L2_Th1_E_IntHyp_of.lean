-- Prove2me | solution 1 for Formalism.L2.Th1.E.IntHyp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:54.226925+00:00
-- url     : https://prove2.me/submissions/416d7283-c494-4b64-8c0a-d40322d43c27

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_isPt_X
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_cc_phSum
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_subst_phSum
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_integral_iff
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_X
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_flin


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)
open Formalism.L2.Th1.C (IntMv IntPS IsPt)
open CompatibleChartOperations
namespace Formalism.L2.Th1.E
theorem _root_.solution (hP : ProdInt) (hS : SubstExpInt) (hC : CongIffSimeq)
    (hH : Formalism.L2.Th1.C.HyperbolicSum) (_hPt : Formalism.L2.Th1.C.PtClosure) : IntHyp := by
  intro K _ _ _ R hR l linv ph hFr O _ _ τ hEnd hBin hF1 hN hA n ι _ _ _ f f' hff hff' hd κ _ r V hr hV
  obtain ⟨hlp, hFG, hph⟩ := hFr
  have hpt : ∀ i, IsPt R (hypCoord l linv τ f f' i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hlp hFG (by rintro (e | e) <;> exact hEnd _)
      (by rintro (e | e) <;> exact isPt_X _)
  obtain ⟨h1, h2⟩ := hP K κ n ph r V hph hr hV
  obtain ⟨h3, h4, h5⟩ := hS K n (Bool × ι) (hypCoord l linv τ f f') (fun i => (hpt i).1)
    (fun i => (integral_iff hR _).2 (hpt i).2) (phSum ph) (thetaProd r V) (cc_phSum hph) h2
  refine ⟨_, _, h4, h5, (hC K R hR _ _ _).1 ?_, by rw [h1, h3]⟩
  rw [subst_phSum ph fun i => (hpt i).1]
  exact hH K R l linv ph ⟨hlp, hFG, hph⟩ O τ hEnd hBin hF1 hN hA n ι f f' hff hff' hd (Bool × ι)
    (fun e => MvPowerSeries.X (false, e)) (fun e => MvPowerSeries.X (true, e))
    (fun e => isPt_X _) (fun e => isPt_X _)
end Formalism.L2.Th1.E
