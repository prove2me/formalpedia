-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.odd_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:13.740494+00:00
-- url     : https://prove2.me/submissions/b527a190-0f03-46d7-8875-2e28d633b2e5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Group
namespace Formalism.FrobeniusOrbits.Group
theorem _root_.solution (e : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) : Odd l := by
  by_contra hl
  rw [Int.not_odd_iff_even] at hl
  obtain ⟨c, rfl⟩ := hl
  have h1 : ((c + c : ℤ) : ZMod (2 ^ (e + 2))) * ((u⁻¹ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1 := by
    rw [← hu, Units.mul_inv]
  have h2 := congrArg (ZMod.castHom (dvd_pow_self 2 (by omega : e + 2 ≠ 0)) (ZMod 2)) h1
  rw [map_mul, map_one, map_intCast] at h2
  have h3 : ((c + c : ℤ) : ZMod 2) = 0 := by
    first
      | (rw [Int.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul])
      | (rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨c, by push_cast; ring⟩)
  rw [h3, zero_mul] at h2
  exact zero_ne_one h2
end Formalism.FrobeniusOrbits.Group
