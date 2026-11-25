-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.weighted_mean_lemma_of_slopes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:36.9329+00:00
-- url     : https://prove2.me/submissions/d75e0df2-79dc-4d02-bd7f-2190e6864952

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_pair_of_slopes
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedMeanLemmas_weighted_mean_claimU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution : LemmaUFinitePlaceFamily := by
  intro K _ _ _ _ J _ _ V ι _ _ _ _ _ _ b X hX σ τ M N β Sg0 dr h hM hM0 hN hrk hβ hSg hdr
  refine Formalism.LFunctionChainParameters.WeightedMeanLemmas.weighted_mean_claimU J _ _ _ _ _ h dr _ Sg0 (fun u => ?_) hdr
    (slope_pair_of_slopes K J V ι b X hX σ τ M N β Sg0 dr hM hM0 hN hrk hβ hSg)
  have hfd : FiniteDimensional K (V u) := Module.Finite.of_basis (b u)
  exact_mod_cast rkK_pos (hM0 u)
end Formalism.LFunctionChainParameters.slopeLatticeData
