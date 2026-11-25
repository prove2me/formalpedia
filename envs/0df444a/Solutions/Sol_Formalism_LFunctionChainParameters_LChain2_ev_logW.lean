-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_logW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:38.571316+00:00
-- url     : https://prove2.me/submissions/d89fcd92-dfca-4132-ae0c-b6e0a941b674

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
theorem _root_.solution (x k : ℝ) (Mw : ℕ) (h48 : 48 ≤ x) (hk2 : x ^ 2 ≤ k) (hM0 : 0 < Mw) (hMx : (Mw : ℝ) < x + 1) :
    Real.log (Mw : ℝ) ≤ (k - 3) * Real.log 2 := by
  have hMp : (0 : ℝ) < (Mw : ℝ) := by exact_mod_cast hM0
  have h1 := Real.log_le_sub_one_of_pos hMp
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : (3 : ℝ) ≤ x ^ 2 := by nlinarith
  have h2 : (x ^ 2 - 3) * (1 / 2) ≤ (k - 3) * Real.log 2 :=
    mul_le_mul (by linarith) hl2 (by norm_num) (by linarith)
  nlinarith
end Formalism.LFunctionChainParameters.LChain2
