-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.Model.log_wM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:29.264109+00:00
-- url     : https://prove2.me/submissions/8fd96bd0-b3b4-41c1-b987-c1572a4e3cdf

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_wM_cases

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
open Formalism.LFunctionChainParameters.LChain.Model
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain.Model
theorem _root_.solution (u0 : H) (j : Fin 1) (ρ : E0 × H) : 0 ≤ Real.log (wM u0 j ρ) ∧ Real.log (wM u0 j ρ) ≤ 60 := by
  have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases wM_cases u0 j ρ with h | h <;> rw [h, Real.log_pow] <;> constructor <;> push_cast <;> nlinarith
end Formalism.LFunctionChainParameters.LChain.Model
