-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.sum_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:30.385811+00:00
-- url     : https://prove2.me/submissions/584691a1-fab1-4507-87b5-01891010997a

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_sum_log_norm_over_prime
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_mem_plOver
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_twist_vector_div_ramification

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
variable (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ)
variable {K}
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (hp : p₁.Prime) (S : Finset (slopeLatticeData.FinPl K)) (hS : ∀ w : slopeLatticeData.FinPl K, prBelow w = p₁ → w ∈ S) :
    ∑ w ∈ S, lE w * ((tau0 K p₁ t₁ w : ℝ) / ramE w) = (t₁ : ℝ) * Real.log (p₁ : ℝ) := by
  rw [← sum_log_norm_over_prime S p₁ hp hS, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [twist_vector_div_ramification]
  by_cases h : prBelow w = p₁
  · rw [if_pos ((mem_plOver hp w).2 h), if_pos h]; ring
  · rw [if_neg (fun h' => h ((mem_plOver hp w).1 h')), if_neg h]; ring
end Formalism.LFunctionChainParameters.LChain2
