-- Prove2me | solution 1 for Formalism.HC.Frame.hostOrdersFrob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:53:03.302104+00:00
-- url     : https://prove2.me/submissions/146dd35a-ee9f-4dd8-bbc3-7916eb6ae3d4

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_fst_sq
import Theorems.Thm_Formalism_HC_Frame_hostOrders_of_le

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
theorem _root_.solution (g : φ.GG) :
    orderOf g.2 ∣ orderOf g ∧ orderOf g ∣ 2 * orderOf g.2 ∧
    ∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (φ.e + 2)))ˣ), ((u : ZMod (2 ^ (φ.e + 2))) = (l : ZMod _)) →
      φ.hH g.2 = hcl φ.e u → orderOf g ≤ 2 ^ j →
      ((l : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by
  have h1 : orderOf g.1 ∣ 2 := orderOf_dvd_of_pow_eq_one (φ.fst_sq g)
  have hp : orderOf g = Nat.lcm (orderOf g.1) (orderOf g.2) := Prod.orderOf g
  have hA : orderOf g.2 ∣ orderOf g := by rw [hp]; exact Nat.dvd_lcm_right _ _
  refine ⟨hA, ?_, ?_⟩
  · rw [hp]
    exact Nat.lcm_dvd (dvd_trans h1 (dvd_mul_right 2 _)) (dvd_mul_left _ 2)
  · intro j l u hu ha hj
    exact φ.hostOrders_of_le g.2 j l u hu ha (le_trans (Nat.le_of_dvd (orderOf_pos g) hA) hj)
end Formalism.HC.Frame
