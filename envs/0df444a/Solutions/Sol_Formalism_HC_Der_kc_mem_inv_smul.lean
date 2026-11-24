-- Prove2me | solution 1 for Formalism.HC.Der.kc_mem_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:44.310591+00:00
-- url     : https://prove2.me/submissions/7a2ec221-4718-4ee5-acf0-688c357899cb

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_mem_one_iff
import Theorems.Thm_Formalism_HC_Der_kc_integ_iff
import Theorems.Thm_Formalism_HC_Der_kc_smul_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HC.Der
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) (y : H.E) :
    σ y ∈ ((σ • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
  have hB' : (B : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
  have hσB : ((σ • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H σ B hB)
  rw [FractionalIdeal.mem_inv_iff hσB, FractionalIdeal.mem_inv_iff hB']
  constructor
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    have hb' : σ • b ∈ σ • B := by
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact hb
    have := h (algebraMap (𝓞 H.E) H.E (σ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ • b, hb', rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    rw [show algebraMap (𝓞 H.E) H.E (σ • b) = σ (algebraMap (𝓞 H.E) H.E b) from rfl, ← map_mul,
      kc_integ_iff] at this
    exact this
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have := h (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ⁻¹ • b, hb, rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    have e : σ (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) = algebraMap (𝓞 H.E) H.E b := by
      show σ (σ⁻¹ (b : H.E)) = b
      rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rw [← kc_integ_iff H σ, map_mul, e] at this
    exact this
end Formalism.HC.Der
