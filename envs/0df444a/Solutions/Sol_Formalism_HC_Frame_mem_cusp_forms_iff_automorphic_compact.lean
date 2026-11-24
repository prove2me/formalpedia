-- Prove2me | solution 1 for Formalism.HC.Frame.mem_cusp_forms_iff_automorphic_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:59:56.140553+00:00
-- url     : https://prove2.me/submissions/cd097812-1bc4-4ed6-919b-46b52e72f0d0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_n0_pos
import Theorems.Thm_Formalism_HC_Frame_digit_mem_cyclic_subgroup

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
theorem _root_.solution (t : φ.A) : t ∈ φ.A0 ↔ ∃ s < φ.n0, t = φ.dig s := by
  constructor
  · intro ht
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 ht
    have hn : (0 : ℤ) < φ.n0 := by exact_mod_cast φ.n0_pos
    obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = k % φ.n0 :=
      ⟨(k % φ.n0).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')⟩
    refine ⟨r, ?_, ?_⟩
    · have h1 := Int.emod_lt_of_pos k hn
      rw [← hr] at h1
      exact_mod_cast h1
    · show k • φ.a0 = r • φ.a0
      rw [← natCast_zsmul, hr]
      exact (mod_addOrderOf_zsmul φ.a0 k).symm
  · rintro ⟨s, -, rfl⟩
    exact φ.digit_mem_cyclic_subgroup s
end Formalism.HC.Frame
