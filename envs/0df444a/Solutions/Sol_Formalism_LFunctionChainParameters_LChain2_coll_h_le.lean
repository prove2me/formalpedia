-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.coll_h_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:36.677002+00:00
-- url     : https://prove2.me/submissions/a09f7363-a7b0-4268-af5c-d484ae1f9454

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_scaled_std
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_model_card
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ht_scaled_id
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_dT_nonneg

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
theorem _root_.solution (hT : 4 ≤ T) (hs : ℝ) (hs0 : 0 ≤ hs)
    (hmin : -hs ≤ muMinDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1) (stdLat K _)) (u : Fin Mw) :
    (collFam K v m f T Mw (hbT K f T) gG gE).h u ≤ hs := by
  have hdT := dT_nonneg f T hT
  obtain ⟨ha, -, -⟩ := model_card f T hT
  have : Nonempty (Fin ((T - 2) ^ f)) := ⟨⟨0, ha⟩⟩
  have hsc := (scaled_std K (Fin ((T - 2) ^ f)) (Real.exp (-(dT f T) / 2)) (Real.exp_pos _)).1
  rw [Real.log_exp] at hsc
  refine max_le (le_trans (ht_scaled_id K _ _ (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by linarith))) hs0) ?_
  unfold hbT
  rw [hsc]
  linarith
end Formalism.LFunctionChainParameters.LChain2
