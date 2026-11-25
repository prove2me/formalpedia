-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LSmall.node_sizes_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:29:54.526254+00:00
-- url     : https://prove2.me/submissions/83e0c458-cccd-45ea-b7c2-09ebee85568c

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
import Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_node_sizes_of_windows
import Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_window_sizes_explicit

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
theorem _root_.solution : NodeSizesText := by
  intro H _ _ _ m TT T2 x b b' η κ off bt w h1 h2 h3 h4 h5 h6 h7 h8 h9 hw
  exact node_sizes_of_windows TT T2 x b b' η κ _ off bt w
    (window_sizes_explicit H TT x b b' η κ off bt h1 h2 h3 h4 h5 h6 h7 h8 h9) hw
end Formalism.LFunctionChainParameters.LSmall
