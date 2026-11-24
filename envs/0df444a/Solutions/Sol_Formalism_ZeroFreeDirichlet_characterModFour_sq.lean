-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.characterModFour_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:10.745747+00:00
-- url     : https://prove2.me/submissions/c10d10e0-9c16-4cc6-b966-84ec4ec8703f

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
theorem _root_.solution : characterModFour ^ 2 = 1 := by
  first
    | exact (ZMod.isQuadratic_χ₄.comp _).sq_eq_one
    | exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one
end Formalism.ZeroFreeDirichlet
