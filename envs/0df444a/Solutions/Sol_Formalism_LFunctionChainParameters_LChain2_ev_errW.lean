-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_errW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:11:28.464488+00:00
-- url     : https://prove2.me/submissions/e85e02e4-044f-4ea3-ae11-169d0b3b14c8

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ev_logW
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ev_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (x ε lg : ℝ) (m N Mw : ℕ) (TT T2 : Finset H) (Fm : H → Fam (Fin Mw) m) (h48 : 48 ≤ x)
    (g3 : ErrWindows (ModelText.textData x ε m TT T2) ModelText.CF (XppTx x ε (Fintype.card H)) 15 2)
    (hM0 : 0 < Mw) (hM1 : (Mw : ℝ) < x + 1) :
    ErrWindows (mkData (evG x ε lg) evC.cHH Model.DA (fun _ => 0) N TT T2 (fun _ => aTx x ε)
      (ModelText.wF x ε m TT T2) Fm) evC (XppH H (evG x ε lg)) 15 4 := by
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := g3
  have hε0 : 0 < ε := w2
  have hx1 : 1 ≤ x := by linarith only [h48]
  have hlogb : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  refine ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, ?_, ?_, w15, w16, w17, w18, w19, w20, w21, w22, w23,
    ?_, ?_, ?_, le_rfl, ?_⟩, ?_⟩
  · show 0 ≤ Real.log (bTx x ε)
    rw [hlogb]; exact w13
  · show Real.log (bTx x ε) ≤ 2 * x ^ ε
    rw [hlogb]; exact w14
  · intro u0
    show Real.log ((Fintype.card (Fin Mw) : ℕ) : ℝ) ≤ (ModelText.kTx x ε - 3) * Real.log 2
    rw [Fintype.card_fin]
    refine ev_logW x _ Mw h48 ?_ hM0 hM1
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε0] : (2 : ℝ) ≤ (9 : ℝ) / 2 + 10 * ε)
    rwa [Real.rpow_two] at this
  · show (1 : ℝ) / 4 ≤ 1 / 2
    norm_num
  · show 0 ≤ 6 * x ^ (-(1 : ℝ))
    have := Real.rpow_nonneg (by linarith only [h48] : (0 : ℝ) ≤ x) (-(1 : ℝ))
    linarith only [this]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [evC]
  · exact ev_trace x (x ^ ε) (bTx x ε) (Fintype.card TT : ℝ) h48 (Real.one_le_rpow hx1 hε0.le) (Real.exp_pos _) w6
end Formalism.LFunctionChainParameters.LChain2
