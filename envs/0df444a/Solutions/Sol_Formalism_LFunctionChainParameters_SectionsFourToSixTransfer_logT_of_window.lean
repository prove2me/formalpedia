-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.logT_of_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:55.940193+00:00
-- url     : https://prove2.me/submissions/7d54c64c-ca94-40ad-95aa-d129735ae6f0

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_logT_bounds
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_fk_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution {D : Data U0 W Top m f} {c5 Gam : ℝ} {X : ∀ u0, W u0 → ℝ}
    (hW : CountWindows D c5 Gam) (hLW : LevelWindow D Gam X) (u0 : U0) (u : W u0) :
    Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ Real.log (D.T u0 u) ∧
    Real.log (D.T u0 u) ≤ Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) + 1 / ((f : ℝ) * D.k) := by
  obtain ⟨hX, h1, h2⟩ := hLW u0 u
  have hy := (fk_pos hW).1
  obtain ⟨_, _, _, hG, hlG, _⟩ := hW
  rw [hlG]
  exact logT_bounds hX hG hy h1 h2
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
