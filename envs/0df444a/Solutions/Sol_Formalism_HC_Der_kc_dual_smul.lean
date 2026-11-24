-- Prove2me | solution 1 for Formalism.HC.Der.kc_dual_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:30:23.561109+00:00
-- url     : https://prove2.me/submissions/5b4541e4-8de5-49e9-90d7-79e3396e991d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_sum_comm
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
private theorem isIntegral_algEquiv_apply_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) : IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)
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
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (y : H.E)
    (hy : ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) :
    ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x)) := by
  intro x
  have hx := hy (σ⁻¹ • x)
  have hx' : σ ((σ⁻¹ • x : 𝓞 H.E) : H.E) = (x : H.E) := by
    show σ (σ⁻¹ (x : H.E)) = x
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have e : ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x) =
      σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * ((σ⁻¹ • x : 𝓞 H.E) : H.E))) := by
    rw [kc_sum_comm H σ hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul σ, hx']
  rw [e, isIntegral_algEquiv_apply_iff]
  exact hx
end Formalism.HC.Der
