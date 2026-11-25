-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_total_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:26:05.993481+00:00
-- url     : https://prove2.me/submissions/19c80afb-1ade-47b1-a100-a0ef00691b82

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_le_three_halves
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sg1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_sharp_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_unitU_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : WindowSizeBound := by
  intro P e K m T hW hL hm hT
  have h := size_sharp_bound P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hU := unitU_nonneg (P := P) hm hT
  have h1 : 2 * Real.log 4 * P.C + 13 * sg P K ≤ 3 * P.C + 13 := by
    have := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 3 by linarith [log_four_le_three_halves]) F.C0
    linarith [F.sg1]
  exact h.trans (mul_le_mul_of_nonneg_right h1 hU)
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
