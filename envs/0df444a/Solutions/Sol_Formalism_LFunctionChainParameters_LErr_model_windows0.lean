-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.model_windows0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:07.95162+00:00
-- url     : https://prove2.me/submissions/c4cb78c3-23e1-4293-9746-44723e26a081

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution (η cHH : ℝ) (hη : 0 ≤ η) (hc : 0 ≤ cHH) :
    ErrWindows0 (modelD η) (modelC cHH) 3 1 1 := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨by norm_num [modelD], by norm_num [modelD], by norm_num [modelD], by norm_num [modelD],
    by norm_num [modelD], by simp [Data.nT], by norm_num [modelD], by norm_num [modelD],
    by norm_num, by norm_num [modelD], by norm_num [modelD], by norm_num [modelD],
    by norm_num [modelD], by norm_num [modelD], by norm_num [modelD], by norm_num [modelD],
    by norm_num [modelD], by norm_num [modelD], by norm_num, by norm_num [modelD],
    fun _ => by norm_num [modelD], by norm_num [modelD], by norm_num [modelD], fun _ => ?_,
    by norm_num [modelD], hη, by norm_num [modelD], ?_⟩
  · simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
    exact mul_nonneg (by norm_num [modelD]) hl2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc⟩ <;> norm_num [modelC]
end Formalism.LFunctionChainParameters.LErr
