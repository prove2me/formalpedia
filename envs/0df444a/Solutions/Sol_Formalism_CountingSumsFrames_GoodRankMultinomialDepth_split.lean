-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GoodRankMultinomialDepth.split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:14.250198+00:00
-- url     : https://prove2.me/submissions/84a6e0d9-377d-4586-a71b-a5824d380516

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.GoodRankMultinomialDepth
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.CountingSumsFrames.GoodRankMultinomialDepth
theorem _root_.solution {B : Type} [AddCommGroup B] [Module O B] {π : O} (hπ : Irreducible π) (E σ : ℕ)
    (g : (Fin σ → O) →ₗ[O] B) :
    ∃ (p : Fin σ → Prop) (j0 : ({k // p k} → O) →ₗ[O] (Fin σ → O))
      (j1 : ({k // ¬ p k} → O) →ₗ[O] (Fin σ → O)),
      (∀ x, ∃ z, g (j0 x) = π ^ (E + 1) • z) ∧
      (∀ x y, j0 x = π • y → ∀ i, π ∣ x i) ∧
      (∀ x z, g (j1 x) = π ^ (E + 1) • z → ∀ i, π ∣ x i) := by
  classical
  let Z0 : Submodule O (Fin σ → O) :=
    { carrier := {x | ∃ z, g x = π ^ (E + 1) • z}
      add_mem' := by
        rintro a b ⟨z1, h1⟩ ⟨z2, h2⟩
        exact ⟨z1 + z2, by rw [map_add, h1, h2, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r a ⟨z, hz⟩
        exact ⟨r • z, by rw [map_smul, hz, smul_comm]⟩ }
  have hZ : ∀ x, x ∈ Z0 ↔ ∃ z, g x = π ^ (E + 1) • z := fun x => Iff.rfl
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin σ)) Z0
  let p : Fin σ → Prop := fun k => ∃ i, snf.f i = k ∧ IsUnit (snf.a i)
  let e0 : ({k // p k} → O) →ₗ[O] (Fin σ → O) :=
    LinearMap.pi (fun k => if hk : p k then LinearMap.proj (⟨k, hk⟩ : {k // p k}) else 0)
  let e1 : ({k // ¬ p k} → O) →ₗ[O] (Fin σ → O) :=
    LinearMap.pi (fun k => if hk : ¬ p k then LinearMap.proj (⟨k, hk⟩ : {k // ¬ p k}) else 0)
  have he0 : ∀ x (i : {k // p k}), e0 x i.1 = x i := by
    intro x i
    simp [e0, i.2]
  have he0' : ∀ x (k : Fin σ), ¬ p k → e0 x k = 0 := by
    intro x k hk
    simp [e0, hk]
  have he1 : ∀ x (i : {k // ¬ p k}), e1 x i.1 = x i := by
    intro x i
    simp [e1, i.2]
  have hcoef : ∀ F k, snf.bM.repr (snf.bM.equivFun.symm F) k = F k := by
    intro F k
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨p, snf.bM.equivFun.symm.toLinearMap ∘ₗ e0,
    snf.bM.equivFun.symm.toLinearMap ∘ₗ e1, ?_, ?_, ?_⟩
  · intro x
    rw [← hZ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hk : p k
    · obtain ⟨i, rfl, u, hu⟩ := hk
      have hmem : snf.bM (snf.f i) ∈ Z0 := by
        have hb : snf.bM (snf.f i) = ((u⁻¹ : Oˣ) : O) • (snf.bN i : Fin σ → O) := by
          rw [snf.snf i, smul_smul, ← hu, Units.inv_mul, one_smul]
        rw [hb]
        exact Z0.smul_mem _ (snf.bN i).2
      exact Z0.smul_mem _ hmem
    · rw [he0' x k hk, zero_smul]
      exact Z0.zero_mem
  · intro x y hxy i
    have h1 := congrArg (fun m => snf.bM.repr m i.1) hxy
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoef, he0, map_smul,
      Finsupp.smul_apply, smul_eq_mul] at h1
    exact ⟨_, h1⟩
  · intro x z hxz i
    have hm : (snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x ∈ Z0 := (hZ _).mpr ⟨z, hxz⟩
    have hc : snf.bM.repr ((snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x) i.1 = x i := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoef, he1]
    by_cases hr : i.1 ∈ Set.range snf.f
    · obtain ⟨j, hj⟩ := hr
      have h2 : snf.bM.repr ((snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x) (snf.f j) =
          snf.bN.repr (snf.a j • (⟨_, hm⟩ : Z0)) j :=
        snf.repr_apply_embedding_eq_repr_smul (⟨_, hm⟩ : Z0) (i := j)
      rw [hj, map_smul, Finsupp.smul_apply, smul_eq_mul, hc] at h2
      have hnu : ¬ IsUnit (snf.a j) := fun hu => i.2 ⟨j, hj, hu⟩
      have hπa : π ∣ snf.a j := by
        have hmax : snf.a j ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
          Ideal.mem_span_singleton] at hmax
        exact hmax
      rw [h2]
      exact Dvd.dvd.mul_right hπa _
    · have h3 : snf.bM.repr ((snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x) i.1 = 0 :=
        snf.repr_eq_zero_of_notMem_range ⟨_, hm⟩ hr
      rw [hc] at h3
      rw [h3]
      exact dvd_zero π
end Formalism.CountingSumsFrames.GoodRankMultinomialDepth
