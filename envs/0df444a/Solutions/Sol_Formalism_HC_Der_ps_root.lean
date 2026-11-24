-- Prove2me | solution 1 for Formalism.HC.Der.ps_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:11.191519+00:00
-- url     : https://prove2.me/submissions/10e45897-7f99-4c08-954f-6bf00130ac89

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_gal_conj
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∃ a : H.E, a ≠ 0 ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ a = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * a := by
  let χ : (H.E ≃ₐ[ℚ] H.E) →* ℤˣ := φ.chQ.comp H.gal.toMonoidHom
  have hχ : ∀ σ, (H.gal σ).1.1 = χ σ := fun _ => rfl
  have hs : χ H.conj = -1 := by rw [← hχ, gal_conj]; rfl
  have h1 : H.conj ∉ (fixedField χ.ker).fixingSubgroup := by
    rw [fixingSubgroup_fixedField, MonoidHom.mem_ker, hs]
    decide
  rw [IntermediateField.mem_fixingSubgroup_iff] at h1
  push Not at h1
  obtain ⟨x, hx, hne⟩ := h1
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hx' : ∀ σ, χ σ = 1 → σ x = x := fun σ h => hx σ h
  refine ⟨x - H.conj x, fun h => hne (sub_eq_zero.mp h).symm, fun σ => ?_⟩
  rw [hχ, map_sub]
  rcases Int.units_eq_one_or (χ σ) with h | h
  · have h2 := hx' (H.conj⁻¹ * (σ * H.conj)) (by rw [map_mul, map_mul, map_inv, h, one_mul, inv_mul_cancel])
    have h3 : σ (H.conj x) = H.conj x := by
      have h4 := congrArg H.conj h2
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel_left] at h4
    rw [h, hx' σ h, h3]
    simp
  · have h2 := hx' (H.conj⁻¹ * σ) (by rw [map_mul, map_inv, h, hs, inv_mul_cancel])
    have h3 : σ x = H.conj x := by
      have h4 := congrArg H.conj h2
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel_left] at h4
    have h4 : σ (H.conj x) = x := hx' (σ * H.conj) (by rw [map_mul, h, hs]; decide)
    rw [h, h3, h4]
    simp
end Formalism.HC.Der
