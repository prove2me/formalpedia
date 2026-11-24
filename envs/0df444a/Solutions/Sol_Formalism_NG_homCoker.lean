-- Prove2me | solution 1 for Formalism.NG.homCoker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:41.003375+00:00
-- url     : https://prove2.me/submissions/b7195c9a-f06c-43f0-8c00-2e3b8dc2a8e8

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul

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
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatHomCoker := by
  intro R O M _ _ _ _ _ _ m g _ _ _ Θ
  exact ⟨homEquiv Θ⟩
end Formalism.NG
