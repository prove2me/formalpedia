-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_top_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:30.929213+00:00
-- url     : https://prove2.me/submissions/1674cd17-9ccc-4619-b81c-1d26125f49ef

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
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_landauIteratedDerivatives_key


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
theorem _root_.solution (c m A lA lT lg γ lx xe l2 E1 E2 : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlg : m * lg = lT - m * (l2 + xe)) (hlA : lA = lx + xe) (h : 2 + γ + l2 ≤ lx) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) :
    c * (m * A) ≤ c * (m * ((A * lA - A) - A * γ) - A * lT) + m * (c * A) * lg + E1 + E2 := by
  have key : c * (m * ((A * lA - A) - A * γ) - A * lT) + m * (c * A) * lg = c * (m * A) * (lx - 1 - γ - l2) := by
    have h1 : m * (c * A) * lg = c * A * (m * lg) := by ring
    rw [h1, hlg, hlA]; ring
  rw [key]
  have h2 : c * (m * A) * 1 ≤ c * (m * A) * (lx - 1 - γ - l2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith
end Formalism.LFunctionChainParameters.LChain2
