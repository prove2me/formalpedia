-- Prove2me | solution 1 for Formalism.Q3.mqGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:13.546262+00:00
-- url     : https://prove2.me/submissions/0572101f-fdd8-41a0-a9e7-29298bd222ab

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
import Theorems.Thm_Formalism_Q3_mq_sigma
import Theorems.Thm_Formalism_Q3_mq_galSign_mul
import Theorems.Thm_Formalism_Q3_mq_injective
import Theorems.Thm_Formalism_Q3_mq_isGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution : MQGalois := by
  intro k E _ _ a α h ha
  exact ⟨mq_isGalois h, mq_sigma h, mq_galSign_mul h ha, mq_injective h⟩
end Formalism.Q3
