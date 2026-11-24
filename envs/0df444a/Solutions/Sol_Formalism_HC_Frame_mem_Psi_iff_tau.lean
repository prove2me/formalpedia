-- Prove2me | solution 1 for Formalism.HC.Frame.mem_Psi_iff_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:57:59.080346+00:00
-- url     : https://prove2.me/submissions/930fec97-d604-4bba-aea2-b580be26c167

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_tau1_mem_Psi
import Theorems.Thm_Formalism_HC_Frame_doubling_mem_character_set
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
theorem _root_.solution (g : φ.GG) : g ∈ φ.Psi ↔ (∃ t, g = φ.tau1 t) ∨ (∃ t, g = φ.tau2 t) := by
  constructor
  · intro hg
    rw [mem_Psi_iff] at hg
    obtain ⟨⟨q, d⟩, a⟩ := g
    simp only at hg
    subst hg
    rcases Int.units_eq_one_or q with rfl | rfl
    · exact Or.inl ⟨φ.iotaInv a, rfl⟩
    · exact Or.inr ⟨φ.iotaInv a, rfl⟩
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact φ.tau1_mem_Psi t
    · exact φ.doubling_mem_character_set t
end Formalism.HC.Frame
