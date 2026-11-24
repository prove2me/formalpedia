-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.uniform_bound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:23.006573+00:00
-- url     : https://prove2.me/submissions/8271aacd-6019-44be-b7aa-430988b15abc

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_losses_of_losses5
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_weighted_mean_bound_statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.RankGapBounds.WeightedMeanData
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
theorem _root_.solution {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : MeanBoundWith D C Xpp := by
  intro hne hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  exact weighted_mean_bound_statement D C Xpp hne hS hDIV hE hH hCount hSl hSN
    (losses_of_losses5 D C hLoss) hSI hHH hFP
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
