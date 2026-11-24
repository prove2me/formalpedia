-- Prove2me | solution 1 for Formalism.HC.Frame.TwoGroup.even_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:37.1257+00:00
-- url     : https://prove2.me/submissions/b057ae72-16e1-47b8-8352-6d74d29d83f9

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
theorem _root_.solution (h2 : φ.TwoGroup) {a : φ.MA} (ha : a ≠ 1) : Even (orderOf a) := by
  obtain ⟨i, hi⟩ := h2.orderOf_eq a
  rw [hi]
  refine Nat.even_pow.2 ⟨even_two, ?_⟩
  rintro rfl
  exact ha (orderOf_eq_one_iff.1 (by rw [hi, pow_zero]))
end TwoGroup
end Formalism.HC.Frame
