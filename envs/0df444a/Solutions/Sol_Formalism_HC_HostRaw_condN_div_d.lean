-- Prove2me | solution 1 for Formalism.HC.HostRaw.condN_div_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:54.642796+00:00
-- url     : https://prove2.me/submissions/8d25b12a-1921-4a5c-b71e-5e187a655f9b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam

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
theorem _root_.solution : H.condN / H.d = H.QS * H.q := by
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  rw [HostRaw.condN, Nat.mul_div_cancel _ hd.pos]
end Formalism.HC.HostRaw
