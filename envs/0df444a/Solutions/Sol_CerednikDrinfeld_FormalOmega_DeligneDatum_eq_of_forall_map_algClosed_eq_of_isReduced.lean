-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_algClosed_eq_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6d17831f-1c12-5e7f-a6a8-125d291a1d25

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega
open scoped TensorProduct
open LT.LatticeTree TensorProduct

theorem N4Aux.line_le_of_forall_map_eq
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsReduced B]
    (e e' : DeligneDatum (K := K) π B)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra 𝒪 Ω] (f : B →ₐ[𝒪] Ω),
      DeligneDatum.map (K := K) π f e = DeligneDatum.map (K := K) π f e')
    (M : FullLattice 𝒪 K) : e.line M ≤ e'.line M := by
  intro x hx
  haveI := e'.invertible M
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← Module.forall_dual_apply_eq_zero_iff B]
  intro φ
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro 𝔭 h𝔭
  haveI := h𝔭

  let Ω : Type := AlgebraicClosure (FractionRing (B ⧸ 𝔭))
  let f : B →ₐ[𝒪] Ω := IsScalarTower.toAlgHom 𝒪 B Ω
  have hf : ∀ b, algebraMap B Ω b = f b := fun _ => rfl

  suffices hzero : f (φ ((e'.line M).mkQ x)) = 0 by
    have h0 : algebraMap B Ω (φ ((e'.line M).mkQ x)) = 0 := hzero
    rwa [IsScalarTower.algebraMap_apply B (B ⧸ 𝔭) Ω,
      IsScalarTower.algebraMap_apply (B ⧸ 𝔭) (FractionRing (B ⧸ 𝔭)) Ω,
      map_eq_zero_iff _ (algebraMap (FractionRing (B ⧸ 𝔭)) Ω).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (B ⧸ 𝔭) (FractionRing (B ⧸ 𝔭))),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h0

  let ψ : latticeBaseChange 𝒪 K Ω M →ₗ[Ω] Ω :=
    (AlgebraTensorModule.rid B Ω Ω).toLinearMap ∘ₗ (LinearMap.baseChange Ω φ) ∘ₗ
      Module.Grassmannian.baseChangeMkQ Ω (e'.line M)
  have hψx : ψ (LinearMap.rTensor (↥M.1) f.toLinearMap x) = f (φ ((e'.line M).mkQ x)) := by
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← cancelBaseChange_one_tmul f hf M x, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
      LinearMap.baseChange_tmul, AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
    rfl
  have hψN : ∀ y ∈ lineBaseChange f M (e'.line M), ψ y = 0 := by
    intro y hy
    rw [lineBaseChange_eq_ker f hf M (e'.line M), LinearMap.mem_ker] at hy
    simp only [ψ, LinearMap.comp_apply, hy, map_zero]
  rw [← hψx]
  apply hψN
  have hlines : (DeligneDatum.map (K := K) π f e).line M = (DeligneDatum.map (K := K) π f e').line M := by
    rw [h Ω f]
  change LinearMap.rTensor (↥M.1) f.toLinearMap x ∈ (DeligneDatum.map (K := K) π f e').line M
  rw [← hlines]
  exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsReduced B]
    (d d' : DeligneDatum (K := K) π B)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra 𝒪 Ω] (f : B →ₐ[𝒪] Ω),
      DeligneDatum.map (K := K) π f d = DeligneDatum.map (K := K) π f d') :
    d = d' := by
  apply DeligneDatum.ext'
  funext M
  exact le_antisymm (N4Aux.line_le_of_forall_map_eq π d d' h M)
    (N4Aux.line_le_of_forall_map_eq π d' d (fun Ω _ _ _ f => (h Ω f).symm) M)

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced (solution)
