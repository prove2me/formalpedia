-- Prove2me | solution 1 for Formalism.HC.Der.kc_diff_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:05:57.337971+00:00
-- url     : https://prove2.me/submissions/507e5d15-5363-4fb9-bc19-56a74d167801

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_comm_symm
import Theorems.Thm_Formalism_HC_Der_kc_mem_diff_iff
import Theorems.Thm_Formalism_HC_Der_kc_dual_smul
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
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (z : 𝓞 H.E)
    (hz : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E)) : σ • z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  rw [kc_mem_diff_iff] at hz ⊢
  intro y hy
  have hy' := kc_dual_smul H σ.symm (kc_comm_symm H σ hc) y hy
  have h1 := hz (σ.symm y) hy'
  rw [← isIntegral_algEquiv_apply_iff H σ, map_mul, AlgEquiv.apply_symm_apply] at h1
  have e : ((σ • z : 𝓞 H.E) : H.E) = σ (z : H.E) := rfl
  rw [e]
  exact h1
end Formalism.HC.Der
