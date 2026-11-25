-- Prove2me | solution 1 for Formalism.NG.deltaValLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:18:03.496793+00:00
-- url     : https://prove2.me/submissions/4426bc39-41fd-4ff0-aba3-fb87141ce128

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ProdEraseZero
import Theorems.Thm_Formalism_NG_deltaVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatDeltaValLe := by
  intro l hl hl2 u hu w t
  rw [deltaVal l hl2 u hu w t]
  have := padicValNat_factorial_le (p := l) t
  omega
end Formalism.NG
