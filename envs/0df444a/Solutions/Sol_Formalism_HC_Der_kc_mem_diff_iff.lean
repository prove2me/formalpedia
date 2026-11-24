-- Prove2me | solution 1 for Formalism.HC.Der.kc_mem_diff_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:46:27.83823+00:00
-- url     : https://prove2.me/submissions/53b19696-6881-4e66-9f79-971e2b0a94e8

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_one_ne
import Theorems.Thm_Formalism_HC_Der_kc_mem_dual_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
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


section
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
private theorem mem_one_fractionalIdeal_iff_isIntegral (t : H.E) : t ∈ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
end Formalism.HC.Der
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HC.Der
theorem _root_.solution (z : 𝓞 H.E) :
    z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      ∀ y : H.E, (∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) →
        IsIntegral ℤ ((z : H.E) * y) := by
  have hd : FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
    simpa [FractionalIdeal.dual_eq_zero_iff] using kc_one_ne H
  have e1 : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      (z : H.E) ∈ ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · intro h
      exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, e⟩
      have : w = z := NumberField.RingOfIntegers.ext e
      rwa [← this]
  rw [e1, coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E), FractionalIdeal.mem_inv_iff hd]
  simp only [kc_mem_dual_iff, mem_one_fractionalIdeal_iff_isIntegral]
end Formalism.HC.Der
