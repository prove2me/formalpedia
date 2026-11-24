-- Prove2me | solution 1 for Formalism.HC.Frame.addOrderOf_projection_of_mem_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:56:41.077084+00:00
-- url     : https://prove2.me/submissions/03826a02-6720-4d79-b6e2-2e18e0775ec7

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_eq_zero_of_mem_cyclic_of_projection
import Theorems.Thm_Formalism_HC_Frame_addOrderOf_h_dvd

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
theorem _root_.solution {t : φ.A} (ht : t ∈ φ.A0) : addOrderOf (φ.h t) = addOrderOf t := by
  apply Nat.dvd_antisymm (φ.addOrderOf_h_dvd t)
  apply addOrderOf_dvd_of_nsmul_eq_zero
  apply φ.eq_zero_of_mem_cyclic_of_projection (φ.A0.nsmul_mem ht _)
  rw [map_nsmul, addOrderOf_nsmul_eq_zero]
end Formalism.HC.Frame
