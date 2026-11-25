-- Prove2me | solution 1 for Formalism.HC.Frame.TwoGroup.orderOf_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:57:02.770028+00:00
-- url     : https://prove2.me/submissions/5fb0964f-ed8e-423a-aef2-2eff27abd2c6

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_TwoGroup_orderOf_eq

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
theorem _root_.solution (h2 : φ.TwoGroup) (a : φ.MA) (j : ℕ) : orderOf a ≤ 2 ^ j ↔ a ^ (2 ^ j) = 1 := by
  obtain ⟨i, hi⟩ := h2.orderOf_eq a
  rw [← orderOf_dvd_iff_pow_eq_one, hi, Nat.pow_dvd_pow_iff_le_right (by norm_num),
    Nat.pow_le_pow_iff_right (by norm_num)]
end TwoGroup
end Formalism.HC.Frame
