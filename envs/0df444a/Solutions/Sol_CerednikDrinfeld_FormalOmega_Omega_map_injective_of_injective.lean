-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.map_injective_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9cb1471a-1e27-5be5-b3d8-e0b58635e622

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace OmegaInj21

open CerednikDrinfeld.FormalOmega

theorem tmul_eq_zero_imp {R A B : Type} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (hφ : Function.Injective φ)
    {Q : Type} [AddCommGroup Q] [Module A Q] [Module.Projective A Q] (q : Q)
    (h : letI : Algebra A B := φ.toAlgebra; ((1 : B) ⊗ₜ[A] q : B ⊗[A] Q) = 0) : q = 0 := by
  letI : Algebra A B := φ.toAlgebra
  by_contra hq
  have hq' : q ∉ ((⊥ : Ideal A) • ⊤ : Submodule A Q) := by
    rw [Submodule.bot_smul]; exact hq
  obtain ⟨ψ, hψ⟩ := exists_linearMap_apply_not_mem (⊥ : Ideal A) q hq'
  apply hψ
  have h1 : (ψ.baseChange B) ((1 : B) ⊗ₜ[A] q) = 0 := by rw [h, map_zero]
  rw [LinearMap.baseChange_tmul] at h1
  have h2 : (TensorProduct.AlgebraTensorModule.rid A B B) ((1 : B) ⊗ₜ[A] ψ q) = 0 := by rw [h1, map_zero]
  rw [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one] at h2
  change φ (ψ q) = 0 at h2
  rw [← map_zero φ] at h2
  exact (Ideal.mem_bot).mpr (hφ h2)

theorem mem_of_rTensor_mem_lineBaseChange
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {S' B' : Type} [CommRing S'] [Algebra 𝒪 S'] [CommRing B'] [Algebra 𝒪 B'] (φ : S' →ₐ[𝒪] B')
    (hφ : Function.Injective φ) (M : FullLattice 𝒪 K) (N : Submodule S' (latticeBaseChange 𝒪 K S' M))
    (hN : Module.Invertible S' (latticeBaseChange 𝒪 K S' M ⧸ N))
    (x : latticeBaseChange 𝒪 K S' M)
    (hx : LinearMap.rTensor (↥M.1) φ.toLinearMap x ∈ lineBaseChange φ M N) : x ∈ N := by
  letI : Algebra S' B' := φ.toAlgebra
  haveI : IsScalarTower 𝒪 S' B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI := hN
  rw [lineBaseChange_eq_ker φ (fun _ => rfl) M N, LinearMap.mem_ker] at hx

  have hcalc : Module.Grassmannian.baseChangeMkQ B' N (LinearMap.rTensor (↥M.1) φ.toLinearMap x) =
      (1 : B') ⊗ₜ[S'] N.mkQ x := by
    rw [← cancelBaseChange_one_tmul φ (fun _ => rfl) M x, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
  rw [hcalc] at hx
  have := tmul_eq_zero_imp φ hφ (N.mkQ x) hx
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end OmegaInj21

open OmegaInj21 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {S' B' : Type} [CommRing S'] [Algebra 𝒪 S'] [CommRing B'] [Algebra 𝒪 B'] (φ : S' →ₐ[𝒪] B')
    (hφ : Function.Injective φ) : Function.Injective ((Omega K π).map φ) := by
  intro d₁ d₂ h
  apply DeligneDatum.ext'
  funext M
  have hM : lineBaseChange φ M (d₁.line M) = lineBaseChange φ M (d₂.line M) :=
    congrArg (fun d : DeligneDatum (K := K) π B' => d.line M) h
  ext x
  constructor
  · intro hx
    apply mem_of_rTensor_mem_lineBaseChange φ hφ M (d₂.line M) (d₂.invertible M) x
    rw [← hM]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · intro hx
    apply mem_of_rTensor_mem_lineBaseChange φ hφ M (d₁.line M) (d₁.invertible M) x
    rw [hM]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

end S_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective (solution)
