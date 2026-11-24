-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.characterModFour_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:10.038119+00:00
-- url     : https://prove2.me/submissions/99150f71-b508-4df2-89a6-41e245493e69

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_CharExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl
end Formalism.ZeroFreeDirichlet
