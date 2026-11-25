-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:31.213848+00:00
-- url     : https://prove2.me/submissions/360675bc-b04a-4245-9094-de4492e7d1e7

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
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (x xe b c : ℝ) (h48 : 48 ≤ x) (hxe : 1 ≤ xe) (hb : 0 < b) (hc : 1 ≤ c) :
    (6 * x ^ (-(1 : ℝ)) + 4 * Real.sqrt 0) * (x ^ (1 : ℝ) * b) ≤ 4 * xe * (c * (x * b)) := by
  have hx0 : 0 < x := by linarith
  rw [Real.sqrt_zero, mul_zero, add_zero, Real.rpow_neg_one, Real.rpow_one]
  have e : 6 * x⁻¹ * (x * b) = 6 * b := by field_simp
  rw [e]
  have ha0 : 0 < x * b := mul_pos hx0 hb
  have h2 : x * b ≤ c * (x * b) := le_mul_of_one_le_left ha0.le hc
  have h3 : c * (x * b) ≤ xe * (c * (x * b)) := le_mul_of_one_le_left (by positivity) hxe
  have h4 : 6 * b ≤ 4 * (x * b) := by nlinarith
  linarith
end Formalism.LFunctionChainParameters.LChain2
