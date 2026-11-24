-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.losses_of_losses5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:46.368441+00:00
-- url     : https://prove2.me/submissions/59d6a893-677b-48f0-b5d4-548b2665959c

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_const
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_mono


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
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
theorem _root_.solution [Nonempty U0] (h : LossBounds D C) : D.Losses C := by
  refine ⟨?_, ?_⟩
  · have := umean_mono (X := fun u0 => D.ASK u0 - D.Ga u0) (Y := fun _ : U0 => D.LoP C)
      (fun u0 => (h u0).1)
    rwa [umean_const] at this
  · have := umean_mono (X := D.IO) (Y := fun _ : U0 => D.LoP C) (fun u0 => (h u0).2)
    rwa [umean_const] at this
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
