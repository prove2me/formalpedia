-- Prove2me | solution 1 for Formalism.HC.Frame.placeOf_mem_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:02:40.043473+00:00
-- url     : https://prove2.me/submissions/d89e7a6a-8dd6-4755-923c-865aca6739c3

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (g : φ.GG) : placeOf g ∈ φ.Psi := by
  unfold Formalism.HC.Frame.placeOf
  split_ifs with h
  · exact (mem_Psi_iff g).2 h
  · rw [mem_Psi_iff]
    rcases Int.units_eq_one_or g.1.2 with h' | h'
    · exact absurd h' h
    · show (-1 : ℤˣ) * g.1.2 = 1
      rw [h']
      simp
end Formalism.HC.Frame
