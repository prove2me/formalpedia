-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exists_product_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:42.72602+00:00
-- url     : https://prove2.me/submissions/59ff211e-52c5-43ee-a3a8-aef9166b453c

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_CharExists
import Theorems.Thm_Formalism_ZeroFreeDirichlet_isProdChar_changeLevel_mul

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
theorem _root_.solution : ProdCharExists :=
  fun _ _ χ₁ χ₂ => ⟨_, isProdChar_changeLevel_mul χ₁ χ₂⟩
end Formalism.ZeroFreeDirichlet
