-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.diff_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:20.608893+00:00
-- url     : https://prove2.me/submissions/c8718b0a-4f92-4e29-9fb3-0dc6114db16d

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_comm_symm
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_mem_diff_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_dual_smul
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply


section
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end Principal
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Principal
section Invariance
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
private theorem coe_powerSeries_smul_eq_smul (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b)) (z : 𝓞 (hostE ζ a b)) :
    ((σ • z : 𝓞 (hostE ζ a b)) : hostE ζ a b) = σ (z : hostE ζ a b) := by
  first
  | rfl
  | simp
end Invariance
end Principal
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x)) (z : 𝓞 (hostE ζ a b))
    (hz : z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) : σ • z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := by
  rw [mem_diff_iff hqd h] at hz ⊢
  intro y hy
  have h1 := (hz _ (dual_smul σ.symm (comm_symm σ hc) y hy)).map
    ((σ : (hostE ζ a b) →+* (hostE ζ a b)).toIntAlgHom)
  have e : σ (z : hostE ζ a b) * y = σ ((z : hostE ζ a b) * σ.symm y) := by
    rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [coe_powerSeries_smul_eq_smul, e]
  exact h1
end Formalism.FrobeniusOrbits.Principal
