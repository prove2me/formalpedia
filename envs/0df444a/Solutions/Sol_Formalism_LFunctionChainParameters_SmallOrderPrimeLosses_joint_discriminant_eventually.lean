-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.joint_discriminant_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:40.235863+00:00
-- url     : https://prove2.me/submissions/06b0389c-f877-417e-8540-175eb40ecc18

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_joint_discriminant_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_large_x_eventually


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
theorem _root_.solution : LossBoundsEventually := by
  obtain ⟨Cord, h0, h⟩ := joint_discriminant_bound
  refine ⟨Cord, h0, ?_⟩
  intro ε e K hε hε4
  obtain ⟨x₀, hx₀⟩ := large_x_eventually ε e K hε hε4
  refine ⟨x₀, ?_⟩
  intro P hPε hPC hx hW
  exact h P e K hPC hW (by rw [hPε]; exact hx₀ _ hx)
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
