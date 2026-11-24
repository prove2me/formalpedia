-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_Hw_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:18.712877+00:00
-- url     : https://prove2.me/submissions/1ff56796-a0c7-46be-a579-058a52596aa8

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_weight_hom
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_weight_mapDomain
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight_mapDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
universe u
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.WeightCompositions
variable {N n : ℕ}
variable {K : Type u} [Field K] (ν : Fin N → ℕ)
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution (h3p : NormUnitaryPermutationInvariance.{u}) (σ : Equiv.Perm (Fin n)) (w : Fin n → ℕ) :
    Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w) ≤
      Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm)) := by
  let f : Fin N × Fin n → Fin N × Fin n := fun p => (p.1, σ p.2)
  have hf : Function.Injective f := by
    intro a b h
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext h.1 (σ.injective h.2)
  let g : (Fin n → ℕ) →+ (Fin n → ℕ) :=
    { toFun := fun v => v ∘ σ.symm, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hg : (fun i => coordWt N n (f i)) = fun i => g (coordWt N n i) := by
    funext i k
    simp only [coordWt, f, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Pi.single_apply, Equiv.symm_apply_eq]
  have hmem : ∀ F ∈ H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w,
      rename f F ∈ H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm) := by
    intro F hF
    rw [Submodule.mem_inf] at hF ⊢
    refine ⟨h3p K N n ν σ F hF.1, ?_⟩
    have hw := hF.2
    rw [mem_weightedHomogeneousSubmodule] at hw ⊢
    intro d hd
    by_contra hne
    apply hd
    apply coeff_rename_eq_zero
    intro u hu
    by_contra hu0
    apply hne
    rw [← hu, weight_mapDomain, hg, weight_hom, hw hu0]
    rfl
  have : FiniteDimensional K
      ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let L : ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w) →ₗ[K]
      ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm)) :=
    { toFun := fun F => ⟨rename f F, hmem F F.2⟩
      map_add' := by intros; ext1; simp
      map_smul' := by intros; ext1; simp }
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro a b hab
  apply Subtype.ext
  exact rename_injective f hf (congrArg Subtype.val hab)
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
