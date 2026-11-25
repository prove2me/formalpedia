-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.joint_bound_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:56:54.05535+00:00
-- url     : https://prove2.me/submissions/b3147d7c-22dd-4df6-9494-a375b587e75b

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_large_x_eventually
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_joint_size_bound_alt

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
theorem _root_.solution : WindowLossesEventual := by
  obtain ⟨Cord, h0, h⟩ := joint_size_bound_alt
  refine ⟨Cord, h0, ?_⟩
  intro ε e K hε hε4
  obtain ⟨x₀, hx₀⟩ := large_x_eventually ε e K hε hε4
  refine ⟨x₀, ?_⟩
  intro P hPε hPC hx hW
  exact h P e K hPC hW (by rw [hPε]; exact hx₀ _ hx)
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
