-- Prove2me | solution 1 for Formalism.HC.Frame.twHom_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:23.392989+00:00
-- url     : https://prove2.me/submissions/cd2ecb11-1380-460f-a5ea-b558347d68f9

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_chC_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_chC_apply


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
theorem _root_.solution (χ : φ.GG →* ℂˣ) : φ.twHom χ = 1 ↔ χ = φ.chC := by
  constructor
  · intro h
    ext g
    have hg : ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 :=
      congrArg (fun f : φ.GG →* ℂ => f g) h
    have hc : ((φ.chC g : ℂˣ) : ℂ) * ((φ.chC g : ℂˣ) : ℂ) = 1 := by
      rw [φ.chC_apply]
      rcases Int.units_eq_one_or g.1.2 with h1 | h1 <;> rw [h1] <;> norm_num
    have hr : starRingEnd ℂ ((φ.chC g : ℂˣ) : ℂ) = ((φ.chC g : ℂˣ) : ℂ) := by
      rw [φ.chC_apply]
      exact map_intCast _ _
    have h2 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = ((φ.chC g : ℂˣ) : ℂ) := by
      calc _ = ((φ.chC g : ℂˣ) : ℂ) * ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) := by
            rw [hc, one_mul]
        _ = ((φ.chC g : ℂˣ) : ℂ) := by rw [mul_assoc, hg, mul_one]
    have h3 := congrArg (starRingEnd ℂ) h2
    rw [Complex.conj_conj, hr] at h3
    first
    | exact h3
    | exact Units.ext h3
  · rintro rfl
    ext g
    show ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((φ.chC g : ℂˣ) : ℂ) = 1
    rw [φ.chC_apply]
    rcases Int.units_eq_one_or g.1.2 with h1 | h1 <;> rw [h1] <;> norm_num
end Formalism.HC.Frame
