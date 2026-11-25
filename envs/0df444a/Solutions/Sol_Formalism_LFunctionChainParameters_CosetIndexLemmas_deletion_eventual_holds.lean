-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.CosetIndexLemmas.deletion_eventual_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:55:33.873283+00:00
-- url     : https://prove2.me/submissions/48c6abb4-7d63-447f-8a76-d05dc233190c

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
open Filter
namespace Formalism.LFunctionChainParameters.CosetIndexLemmas
theorem _root_.solution : DelEv := by
  intro ε hε
  obtain ⟨x₀, hx₀⟩ := ((tendsto_rpow_atTop (show 0 < ε / 7 by positivity)).eventually_ge_atTop 6).exists_forall_of_atTop
  refine ⟨x₀, fun x del hx hdel => ?_⟩
  have h6 := hx₀ x hx
  refine hdel.trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.add_one_le_exp (x ^ (ε / 7))
  norm_num
  linarith
end Formalism.LFunctionChainParameters.CosetIndexLemmas
