-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.model_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:52.004621+00:00
-- url     : https://prove2.me/submissions/ee5c79f1-3b4e-4d36-bd50-55852e9849d8

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
variable (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ)
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (hT : 4 ≤ T) :
    0 < (T - 2) ^ f ∧ (T - 2) ^ f ≤ (T - 1) ^ f ∧
    Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) = (T - 1) ^ f := by
  have h1 : 0 < (T - 2) ^ f := Nat.pow_pos (by omega)
  have h2 : (T - 2) ^ f ≤ (T - 1) ^ f := Nat.pow_le_pow_left (by omega) f
  refine ⟨h1, h2, ?_⟩
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega
end Formalism.LFunctionChainParameters.LChain2
