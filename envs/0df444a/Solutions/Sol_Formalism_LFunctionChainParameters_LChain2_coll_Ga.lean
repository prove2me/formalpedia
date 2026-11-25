-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.coll_Ga
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:23.923016+00:00
-- url     : https://prove2.me/submissions/a13a2d7a-7192-4eea-82ce-f6e506acb55c

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_twist_vector_at_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_sum_bump
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_mem_second_closed

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
theorem _root_.solution (hm : 1 ≤ m) : (collFam K v m f T Mw hb gG gE).Ga = gG := by
  have hm' : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  show 2 * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * ((∑ _j : Fin m, bump K m gG w) - ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w) = gG
  have h1 : ∀ w ∈ plOver K 2 ∪ plOver K T, lE w * ((∑ _j : Fin m, bump K m gG w) - ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w)
      = (m : ℝ) * (lE w * bump K m gG w) := by
    intro w _
    rw [twist_vector_at_zero]
    simp
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have := sum_bump K m hm gG _ (mem_second_closed K T)
  calc 2 * ((m : ℝ) * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * bump K m gG w)
      = (m : ℝ) * (2 * ∑ w ∈ plOver K 2 ∪ plOver K T, lE w * bump K m gG w) := by ring
    _ = gG := by rw [this]; field_simp
end Formalism.LFunctionChainParameters.LChain2
