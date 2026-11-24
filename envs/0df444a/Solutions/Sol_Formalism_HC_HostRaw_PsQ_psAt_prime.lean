-- Prove2me | solution 1 for Formalism.HC.HostRaw.PsQ.psAt_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:37:44.766586+00:00
-- url     : https://prove2.me/submissions/e0a83de9-0bbd-40df-b508-b56c4bb2daf4

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_HostRaw_PsQ_psAt_eq

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
variable {H}
namespace Formalism.HC.HostRaw
namespace PsQ
theorem _root_.solution (hP : H.PsQ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ H.condN) :
    H.psAt p = jacobiSym (-(H.q : ℤ)) p :=
  hP.psAt_eq ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
end PsQ
end Formalism.HC.HostRaw
