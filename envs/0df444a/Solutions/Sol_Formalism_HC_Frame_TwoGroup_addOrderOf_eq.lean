-- Prove2me | solution 1 for Formalism.HC.Frame.TwoGroup.addOrderOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:57.220219+00:00
-- url     : https://prove2.me/submissions/fcfe594b-f910-422a-9ef2-66ed7e4a67db

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_addOrderOf_dvd_ord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
variable {φ}
namespace Formalism.HC.Frame
namespace TwoGroup
theorem _root_.solution (h2 : φ.TwoGroup) (t : φ.A) : ∃ i : ℕ, addOrderOf t = 2 ^ i := by
  obtain ⟨j, hj⟩ := h2
  have hd : addOrderOf t ∣ 2 ^ j := by
    rw [← hj]
    exact φ.addOrderOf_dvd_ord t
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨i, hi⟩
end TwoGroup
end Formalism.HC.Frame
