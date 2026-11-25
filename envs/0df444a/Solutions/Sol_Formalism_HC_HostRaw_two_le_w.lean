-- Prove2me | solution 1 for Formalism.HC.HostRaw.two_le_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:55:35.264401+00:00
-- url     : https://prove2.me/submissions/b05c3b0b-3261-45ce-a096-a57e710fd1a4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Theorems.Thm_Formalism_HC_HostRaw_w_pos
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution : 2 ≤ H.w := Nat.le_of_dvd H.w_pos H.two_dvd_w
end Formalism.HC.HostRaw
