-- Prove2me | solution 1 for Formalism.HC.Der.kc_mem_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:33.030992+00:00
-- url     : https://prove2.me/submissions/2511d493-cc36-4cf5-a29a-191bbd49331d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_one_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
namespace Formalism.HC.Der
theorem _root_.solution (y : H.E) :
    y ∈ FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x)) := by
  haveI := H.galois
  rw [FractionalIdeal.mem_dual (kc_one_ne H)]
  have key : ∀ w : H.E, Algebra.trace H.K H.E w ∈ (algebraMap (𝓞 H.K) H.K).range ↔
      IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w) := by
    intro w
    rw [← trace_eq_sum_automorphisms, isIntegral_algebraMap_iff (algebraMap H.K H.E).injective]
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      exact NumberField.RingOfIntegers.isIntegral_coe a
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  constructor
  · intro h x
    rw [← key]
    have := h _ ((mem_one_fractionalIdeal_iff_isIntegral H _).mpr (NumberField.RingOfIntegers.isIntegral_coe x))
    rwa [Algebra.traceForm_apply] at this
  · intro h a ha
    rw [mem_one_fractionalIdeal_iff_isIntegral] at ha
    rw [Algebra.traceForm_apply, key]
    exact h ⟨a, ha⟩
end Formalism.HC.Der
