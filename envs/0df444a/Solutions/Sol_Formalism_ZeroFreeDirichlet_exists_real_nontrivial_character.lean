-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exists_real_nontrivial_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:32.434749+00:00
-- url     : https://prove2.me/submissions/d7d6b640-ee18-4c48-a9d3-0a58c6d515d0

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_CharExists
import Theorems.Thm_Formalism_ZeroFreeDirichlet_characterModFour_sq
import Theorems.Thm_Formalism_ZeroFreeDirichlet_characterModFour_ne_one

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
theorem _root_.solution : RealCharExists :=
  ⟨4, ⟨by norm_num⟩, characterModFour, characterModFour_sq, characterModFour_ne_one⟩
end Formalism.ZeroFreeDirichlet
