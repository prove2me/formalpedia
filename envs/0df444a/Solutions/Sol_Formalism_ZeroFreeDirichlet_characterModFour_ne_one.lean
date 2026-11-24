-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.characterModFour_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:44.177546+00:00
-- url     : https://prove2.me/submissions/cc8ca322-9bbb-4731-b3e0-dd023fd2e13b

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_CharExists
import Theorems.Thm_Formalism_ZeroFreeDirichlet_characterModFour_apply

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
theorem _root_.solution : characterModFour ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  rw [characterModFour_apply, MulChar.one_apply hu] at h3
  have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hv] at h3
  norm_num at h3
end Formalism.ZeroFreeDirichlet
