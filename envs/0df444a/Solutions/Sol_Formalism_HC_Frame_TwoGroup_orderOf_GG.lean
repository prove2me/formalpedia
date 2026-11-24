-- Prove2me | solution 1 for Formalism.HC.Frame.TwoGroup.orderOf_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:55.804809+00:00
-- url     : https://prove2.me/submissions/97bdaa7e-1ee4-40ce-9fb7-5f4d96fe8c2a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_natCard_MA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem natCard_int_units_eq_two : Nat.card ℤˣ = 2 := by
  first
  | (rw [Nat.card_eq_fintype_card]; rfl)
  | (rw [Nat.card_eq_fintype_card]; decide)
  | simp
private theorem natCard_GG_eq_four_mul_ord : Nat.card φ.GG = 4 * φ.ord := by
  have h3 : Nat.card φ.GG = Nat.card ℤˣ * Nat.card ℤˣ * Nat.card φ.MA := by
    rw [Nat.card_prod, Nat.card_prod]
  rw [natCard_int_units_eq_two, φ.natCard_MA] at h3
  omega
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
variable {φ}
namespace Formalism.HC.Frame
namespace TwoGroup
theorem _root_.solution (h2 : φ.TwoGroup) (g : φ.GG) : ∃ i : ℕ, orderOf g = 2 ^ i := by
  obtain ⟨j, hj⟩ := h2
  have hd : orderOf g ∣ 2 ^ (j + 2) := by
    convert orderOf_dvd_natCard g using 1
    rw [natCard_GG_eq_four_mul_ord, hj]
    ring
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨i, hi⟩
end TwoGroup
end Formalism.HC.Frame
