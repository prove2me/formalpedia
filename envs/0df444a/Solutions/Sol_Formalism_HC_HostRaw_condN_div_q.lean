-- Prove2me | solution 1 for Formalism.HC.HostRaw.condN_div_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:55.361876+00:00
-- url     : https://prove2.me/submissions/c842f026-9396-40e5-9472-92b6ca0d5ec2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_HC_HostRaw_condN_eq_q

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution : H.condN / H.q = H.QS * H.d := by
  obtain ⟨hq, -, -, -, -⟩ := H.hyp
  rw [condN_eq_q, Nat.mul_div_cancel _ hq.pos]
end Formalism.HC.HostRaw
