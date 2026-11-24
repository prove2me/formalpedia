-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.compl_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:29:14.618796+00:00
-- url     : https://prove2.me/submissions/9895da42-df4f-412a-b569-d93f67aa4d40

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution (D0 : Data U0 W Top m f) (u0 : U0) :
    D0.Main u0 = ∑ t, ((m : ℝ) * (ph (D0.aT t) - D0.aT t * (D0.gam - D0.LpL)) - D0.aT t * sLog D0 u0) := by
  unfold Data.Main sLog ph
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
end Formalism.LFunctionChainParameters.LChain
