-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.dual_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:14.166321+00:00
-- url     : https://prove2.me/submissions/ed5cd252-04e9-439b-8271-b35ef2e292cc

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_sum_comm
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
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
theorem _root_.solution (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x)) (y : (hostE ζ a b))
    (hy : ∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (y * x))) :
    ∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (σ y * x)) := by
  intro x
  have key : (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (σ y * x)) =
      σ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b),
        τ (y * ((σ⁻¹ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b))) := by
    rw [sum_comm σ hc, map_mul, coe_powerSeries_smul_eq_smul, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  rw [key]
  exact (hy (σ⁻¹ • x)).map ((σ : (hostE ζ a b) →+* (hostE ζ a b)).toIntAlgHom)
end Formalism.FrobeniusOrbits.Principal
