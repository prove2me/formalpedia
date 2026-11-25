-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LSmall.window_sizes_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:32.942691+00:00
-- url     : https://prove2.me/submissions/51cb2436-d191-4b78-9583-7b7c705f699e

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LSmall
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
namespace Formalism.LFunctionChainParameters.LSmall
theorem _root_.solution : WindowSizesText := by
  intro H _ _ _ TT x b b' η κ off bt hx hb hb' hη hη4 hκ hκ4 hoff hbt
  have hx0 : 0 < x := by linarith
  have hn : (1 : ℝ) ≤ (Fintype.card H : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H)
  have hq0 : 0 ≤ b' / x := by positivity
  have hq3 : b' / x ≤ b' / 3 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  refine ⟨hb, hb', hη, hκ, hx0, ?_, ?_, by positivity, ?_, hbt, ?_⟩
  · rcases hoff with rfl | rfl
    · exact hq0
    · exact_mod_cast Int.floor_nonneg.2 hq0
  · rcases hoff with rfl | rfl
    · exact le_refl _
    · exact Int.floor_le _
  · apply div_le_div_of_nonneg_left hb'.le hx0
    nlinarith
  · have : κ * b' ≤ 1 / 4 * b' := mul_le_mul_of_nonneg_right hκ4 hb'.le
    linarith
end Formalism.LFunctionChainParameters.LSmall
