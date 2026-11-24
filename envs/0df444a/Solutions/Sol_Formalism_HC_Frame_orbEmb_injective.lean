-- Prove2me | solution 1 for Formalism.HC.Frame.orbEmb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:58:00.017915+00:00
-- url     : https://prove2.me/submissions/08b08a79-4a7c-4701-9dfa-5bcc8179f97c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (τ : φ.GG) : Function.Injective (φ.orbEmb τ) := by
  rintro ⟨s, a⟩ ⟨s', a'⟩ h
  have h1 : (if s = 1 then (1 : G0) else φ.sg.1) * τ.1 = (if s' = 1 then 1 else φ.sg.1) * τ.1 :=
    congrArg Prod.fst h
  have h2 : a * τ.2 = a' * τ.2 := congrArg Prod.snd h
  have h1' := mul_right_cancel h1
  refine Prod.ext ?_ (mul_right_cancel h2)
  have hsg : (φ.sg.1 : G0) ≠ 1 := fun h' => int_units_neg_one_ne_one (congrArg Prod.fst h')
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · rfl
  · rw [if_pos rfl, if_neg int_units_neg_one_ne_one] at h1'
    exact absurd h1'.symm hsg
  · rw [if_neg int_units_neg_one_ne_one, if_pos rfl] at h1'
    exact absurd h1' hsg
  · rfl
end Formalism.HC.Frame
