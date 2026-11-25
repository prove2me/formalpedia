-- Prove2me | solution 1 for Formalism.HC.Frame.addOrderOf_dvd_o_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:00:30.435821+00:00
-- url     : https://prove2.me/submissions/06fa0aec-15dc-49f6-8ff6-8d77d7af1de0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_o_nsmul_of_h_eq_zero

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
namespace Formalism.HC.Frame
theorem _root_.solution (t : φ.A) : addOrderOf t ∣ φ.o * addOrderOf (φ.h t) := by
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [← smul_smul]
  exact φ.o_nsmul_of_h_eq_zero (by rw [map_nsmul, addOrderOf_nsmul_eq_zero])
end Formalism.HC.Frame
