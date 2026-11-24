-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedMeanLemmas.wmean_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:42.939546+00:00
-- url     : https://prove2.me/submissions/bcc6f05a-7722-45eb-b94d-38f6c0864045

import Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedMeanLemmas
open Finset
variable {ι : Type*} [Fintype ι]
namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas
theorem _root_.solution (d X Y : ι → ℝ) :
    wmean d (fun u => X u - Y u) = wmean d X - wmean d Y := by
  unfold wmean
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [mul_sub]
end Formalism.LFunctionChainParameters.WeightedMeanLemmas
