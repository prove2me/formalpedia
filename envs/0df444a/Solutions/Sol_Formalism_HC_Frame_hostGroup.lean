-- Prove2me | solution 1 for Formalism.HC.Frame.hostGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:21.188918+00:00
-- url     : https://prove2.me/submissions/552047c1-faf4-41ab-b9a9-327bddded55e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_natCard_MA
import Theorems.Thm_Formalism_HC_Frame_index_Psi
import Theorems.Thm_Formalism_HC_Frame_cc_notMem_Psi
import Theorems.Thm_Formalism_HC_Frame_sg_mem_Psi
import Theorems.Thm_Formalism_HC_Frame_orderOf_cc
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
namespace Formalism.HC.Frame
theorem _root_.solution : Nat.card φ.GG = 4 * φ.ord ∧ φ.Psi.index = 2 ∧ φ.cc ∉ φ.Psi ∧ φ.sg ∈ φ.Psi ∧
    orderOf φ.cc = 2 := ⟨by rw [natCard_GG_eq_four_mul_ord], φ.index_Psi, φ.cc_notMem_Psi, φ.sg_mem_Psi, φ.orderOf_cc⟩
end Formalism.HC.Frame
