-- Prove2me | solution 1 for Formalism.HC.HostRaw.w_dvd_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:05.876327+00:00
-- url     : https://prove2.me/submissions/5396fa17-d6e3-4011-92b2-d67f5bbc161e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Theorems.Thm_UpperTheory_torsionOrder_dvd_of_algHom
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_condN


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
theorem _root_.solution : H.w ∣ H.condN :=
  UpperTheory.torsionOrder_dvd_of_algHom H.condN (even_iff_two_dvd.2 H.two_dvd_condN) (Nat.pos_of_ne_zero H.condN_ne_zero) H.cycEmb
end Formalism.HC.HostRaw
