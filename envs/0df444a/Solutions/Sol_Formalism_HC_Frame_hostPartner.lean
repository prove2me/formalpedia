-- Prove2me | solution 1 for Formalism.HC.Frame.hostPartner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:57:58.327342+00:00
-- url     : https://prove2.me/submissions/5b598243-2f39-4681-b73f-70aae802d4f2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_cc_mul_cc
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


section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'
private theorem cc_mul_mem_Psi_iff_not_mem (g : φ.GG) : φ.cc * g ∈ φ.Psi ↔ g ∉ φ.Psi := by
  rw [mem_Psi_iff, mem_Psi_iff]
  show (-1 : ℤˣ) * g.1.2 = 1 ↔ ¬ g.1.2 = 1
  rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> simp [int_units_neg_one_ne_one]
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (τ : φ.GG) (hτ : τ ∈ φ.Psi) :
    Set.BijOn (fun g : φ.GG => φ.cc * g * τ) {g | g ∉ φ.Psi} (φ.Psi : Set φ.GG) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact φ.Psi.mul_mem ((cc_mul_mem_Psi_iff_not_mem φ g).2 hg) hτ
  · intro g _ g' _ h
    exact mul_left_cancel (mul_right_cancel h)
  · intro y hy
    refine ⟨φ.cc * y * τ⁻¹, ?_, ?_⟩
    · show φ.cc * y * τ⁻¹ ∉ φ.Psi
      intro hm
      have : φ.cc * y ∈ φ.Psi := by simpa using φ.Psi.mul_mem hm hτ
      exact (cc_mul_mem_Psi_iff_not_mem φ y).1 this hy
    · show φ.cc * (φ.cc * y * τ⁻¹) * τ = y
      rw [← mul_assoc, ← mul_assoc, φ.cc_mul_cc, one_mul, inv_mul_cancel_right]
end Formalism.HC.Frame
