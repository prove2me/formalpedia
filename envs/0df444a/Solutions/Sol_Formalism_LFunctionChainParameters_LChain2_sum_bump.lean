-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.sum_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:26.683562+00:00
-- url     : https://prove2.me/submissions/54f3ffb3-e209-484d-b395-5ce8e1db7e8d

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
theorem _root_.solution (hm : 1 ≤ m) (c : ℝ) (S : Finset (slopeLatticeData.FinPl K)) (hS : ∀ w : slopeLatticeData.FinPl K, prBelow w = 2 → w ∈ S) :
    2 * ∑ w ∈ S, lE w * bump K m c w = c / (m : ℝ) := by
  have hu := sum_log_norm_over_prime S 2 Nat.prime_two hS
  have h1 : ∑ w ∈ S, lE w * bump K m c w = c / (2 * (m : ℝ) * Real.log 2) * ∑ w ∈ S.filter (fun w => prBelow w = 2), lE w := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold bump
    split_ifs <;> ring
  rw [h1, hu]
  have hl : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
    exact this.ne'
  have hm' : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  push_cast at hl ⊢
  field_simp
end Formalism.LFunctionChainParameters.LChain2
