-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ker_includeRight_eq_map_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:11.878443+00:00
-- url     : https://prove2.me/submissions/2b783e27-0cfd-4226-ae39-0e93801cd050

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FunctorialResolution.EmbeddedResolution
private theorem lid_rTensor_subtype_mem_map {R A' : Type*} [CommRing R] [CommRing A'] [Algebra R A']
    (K : Ideal R) (y : K ⊗[R] A') :
    (TensorProduct.lid R A') (LinearMap.rTensor A' K.subtype y) ∈ K.map (algebraMap R A') := by
  induction y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
  | tmul k a =>
      have hka : (TensorProduct.lid R A') (LinearMap.rTensor A' K.subtype (k ⊗ₜ[R] a))
          = (k : R) • a := by simp
      rw [hka, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ k.2)
  | add y z hy hz =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hy hz
private theorem algebraMap_tmul_one_eq_one_tmul_algebraMap {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (a : A) :
    (algebraMap A B a) ⊗ₜ[A] (1 : A') = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by
  calc (algebraMap A B a) ⊗ₜ[A] (1 : A') = (a • (1 : B)) ⊗ₜ[A] (1 : A') := by
        rw [Algebra.algebraMap_eq_smul_one]
    _ = a • ((1 : B) ⊗ₜ[A] (1 : A')) := TensorProduct.smul_tmul' a (1 : B) (1 : A')
    _ = (1 : B) ⊗ₜ[A] (a • (1 : A')) := (TensorProduct.tmul_smul a (1 : B) (1 : A')).symm
    _ = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by rw [Algebra.algebraMap_eq_smul_one]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (R B A' : Type*) [CommRing R] [CommRing B] [CommRing A']
    [Algebra R B] [Algebra R A'] [Module.Flat R A'] :
    RingHom.ker (Algebra.TensorProduct.includeRight : A' →ₐ[R] B ⊗[R] A').toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A') := by
  have hex : Function.Exact ((RingHom.ker (algebraMap R B)).subtype) (Algebra.linearMap R B) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    ext r
    simp [RingHom.mem_ker]
  have hflat : Function.Exact
      (LinearMap.rTensor A' ((RingHom.ker (algebraMap R B)).subtype))
      (LinearMap.rTensor A' (Algebra.linearMap R B)) :=
    Module.Flat.rTensor_exact (R := R) (M := A') hex
  apply le_antisymm
  · intro x hx
    have hx0 : (1 : B) ⊗ₜ[R] x = 0 := by
      simpa [RingHom.mem_ker, Algebra.TensorProduct.includeRight_apply,
        AlgHom.toRingHom_eq_coe] using hx
    have key : (LinearMap.rTensor A' (Algebra.linearMap R B)) ((1 : R) ⊗ₜ[R] x) = 0 := by
      simpa using hx0
    have hmem : (1 : R) ⊗ₜ[R] x ∈
        LinearMap.range (LinearMap.rTensor A' ((RingHom.ker (algebraMap R B)).subtype)) := by
      rw [← LinearMap.exact_iff.mp hflat]
      exact LinearMap.mem_ker.mpr key
    obtain ⟨y, hy⟩ := hmem
    have hx1 : x = (TensorProduct.lid R A') ((1 : R) ⊗ₜ[R] x) := by simp
    rw [hx1, ← hy]
    exact lid_rTensor_subtype_mem_map _ y
  · rw [Ideal.map_le_iff_le_comap]
    intro k hk
    have hk0 : algebraMap R B k = 0 := RingHom.mem_ker.mp hk
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e1 : (Algebra.TensorProduct.includeRight : A' →ₐ[R] B ⊗[R] A')
        (algebraMap R A' k) = 0 := by
      rw [Algebra.TensorProduct.includeRight_apply, ← algebraMap_tmul_one_eq_one_tmul_algebraMap, hk0,
        TensorProduct.zero_tmul]
    exact e1
end FunctorialResolution.EmbeddedResolution
