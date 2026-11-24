-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.key_identity5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:45.486417+00:00
-- url     : https://prove2.me/submissions/1fd52340-6fd1-41e6-8fc7-644fbff752a2

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_key_identity


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
theorem _root_.solution (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * Lam5 D C u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) := by
  have h := D.key_identity C hv hf u0 hw
  unfold Data.abelian₂ at h
  unfold Lam5
  linear_combination h
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
