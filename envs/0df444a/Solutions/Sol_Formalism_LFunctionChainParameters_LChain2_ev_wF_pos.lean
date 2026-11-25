-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_wF_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:15:19.062228+00:00
-- url     : https://prove2.me/submissions/7e578289-a168-4843-88f4-c03c25f4e965

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
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (x ε : ℝ) (m : ℕ) (TT T2 : Finset H)
    (hx : 0 < x) (u0 : H) (j : Fin m) (ρ : E0 × H) : 0 < ModelText.wF x ε m TT T2 u0 j ρ := by
  have hb : 0 < bTx x ε := Real.exp_pos _
  have he : 0 < ModelText.etaTx x ε := Real.exp_pos _
  have hbp : 0 < bpTx x ε := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hn : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : 0 < wppTx x ε (Fintype.card H) := div_pos hbp (mul_pos hx hn)
  unfold ModelText.wF
  split_ifs
  · linarith
  · linarith
  · exact hw
end Formalism.LFunctionChainParameters.LChain2
