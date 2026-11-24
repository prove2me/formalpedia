-- Prove2me | solution 1 for Formalism.HC.Frame.orderOf_of_fst_eq_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:00:35.020528+00:00
-- url     : https://prove2.me/submissions/8e7a2e55-b7da-4d8b-bc71-309ce0868954

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
private theorem sign_group_sq_eq_one_var (x : G0) : x ^ 2 = 1 :=
  Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution {g : φ.GG} (hc : g.1 = c0) : orderOf g = Nat.lcm 2 (orderOf g.2) := by
  have hc0 : orderOf (c0 : G0) = 2 :=
    orderOf_eq_prime (sign_group_sq_eq_one_var _) (fun h => int_units_neg_one_ne_one (congrArg Prod.fst h))
  rw [Prod.orderOf, hc, hc0]
end Formalism.HC.Frame
