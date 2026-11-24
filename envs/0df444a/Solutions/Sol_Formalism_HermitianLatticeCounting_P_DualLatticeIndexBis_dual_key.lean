-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.dual_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:11.766986+00:00
-- url     : https://prove2.me/submissions/bdc92f11-9b25-42d6-8e36-2c00c88bb8a4

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_trForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [Module ℚ U] [IsScalarTower ℚ E U]
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution (h : U →ₗ[E] U →ₗ⋆[E] E) (δ : 𝓞 E) (K : Ideal (𝓞 E))
    (hcod : ∀ z : E, (∃ o : 𝓞 E, (o : E) = (δ : E) * z) ↔
        ∀ a ∈ K, ∃ n : ℤ, Algebra.trace ℚ E (star (a : E) * z) = n)
    (L : Submodule (𝓞 E) U) (x : U) :
    ((δ : E) • x ∈ hdual h (algebraMap (𝓞 E) E).range L.toAddSubgroup) ↔
        ∀ y ∈ K • L, ∃ n : ℤ, trForm h x y = n := by
  have hsm : ∀ (a : 𝓞 E) (x : U), a • x = (a : E) • x := fun a x => (algebraMap_smul E a x).symm
  constructor
  · intro H y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha y hy
      obtain ⟨o, ho⟩ := H y hy
      have h1 : (o : E) = (δ : E) * h x y := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at ho
        exact ho
      obtain ⟨n, hn⟩ := (hcod (h x y)).mp ⟨o, h1⟩ a ha
      refine ⟨n, ?_⟩
      rw [trForm_apply, hsm, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
      exact hn
    · rintro y y' ⟨n, hn⟩ ⟨m, hm⟩
      exact ⟨n + m, by rw [map_add, hn, hm]; push_cast; rfl⟩
  · intro H y hy
    have h1 : ∃ o : 𝓞 E, (o : E) = (δ : E) * h x y := by
      rw [hcod]
      intro a ha
      obtain ⟨n, hn⟩ := H (a • y) (Submodule.smul_mem_smul ha hy)
      refine ⟨n, ?_⟩
      rw [trForm_apply, hsm, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul] at hn
      exact hn
    obtain ⟨o, ho⟩ := h1
    refine ⟨o, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact ho
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
