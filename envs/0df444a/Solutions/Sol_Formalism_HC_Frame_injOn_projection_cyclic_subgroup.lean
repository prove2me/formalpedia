-- Prove2me | solution 1 for Formalism.HC.Frame.injOn_projection_cyclic_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:56:31.521737+00:00
-- url     : https://prove2.me/submissions/26477440-8d8c-4d88-9f92-f64609e28304

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_eq_zero_of_mem_cyclic_of_projection

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
theorem _root_.solution : Set.InjOn φ.h φ.A0 := by
  intro x hx y hy hxy
  exact sub_eq_zero.1 (φ.eq_zero_of_mem_cyclic_of_projection (φ.A0.sub_mem hx hy) (by rw [map_sub, hxy, sub_self]))
end Formalism.HC.Frame
