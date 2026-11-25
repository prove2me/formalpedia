-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ht_scaled_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:38.999548+00:00
-- url     : https://prove2.me/submissions/9afeb001-d277-49a7-9960-2e110a54c3a7

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
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gG gE : ℝ)
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (n : Type) [Fintype n] [DecidableEq n] (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    htMap (Pi.basisFun K n) (fun _ => ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)) (Pi.basisFun K n) (fun _ => 1)
      LinearMap.id ≤ 0 := by
  unfold htMap
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun v _ => ?_)
  refine Real.log_nonpos (sq_nonneg _) ?_
  unfold opNormAt
  rw [LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [inv_one, Matrix.one_mul]
  refine pow_le_one₀ (norm_nonneg _) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) x
      = ((c : ℝ) : ℂ) • x := by
    ext i
    simp [Matrix.toLpLin_apply, Matrix.smul_mulVec]
  rw [this, norm_smul, one_mul]
  have h1 : ‖((c : ℝ) : ℂ)‖ = c := by simp [abs_of_nonneg hc0]
  rw [h1]
  exact mul_le_of_le_one_left (norm_nonneg _) hc
end Formalism.LFunctionChainParameters.LChain2
