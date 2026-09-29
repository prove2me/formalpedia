-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6934a223-9215-5565-b2fb-de48c7c1d5b3

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace SpreadGC9

theorem fg_of_projective_quotient {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Finite R V]
    (N : Submodule R V) [Module.Projective R (V ⧸ N)] : N.FG := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id : (V ⧸ N) →ₗ[R] (V ⧸ N)) N.mkQ_surjective
  let p : V →ₗ[R] V := LinearMap.id - s.comp N.mkQ
  have hp : ∀ x, p x ∈ N := fun x => by
    rw [← Submodule.ker_mkQ N, LinearMap.mem_ker]
    change N.mkQ (x - s (N.mkQ x)) = 0
    rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
  have hsurj : Function.Surjective (p.codRestrict N hp) := by
    rintro ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    change x - s (N.mkQ x) = x
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero, sub_zero]
  exact Module.Finite.iff_fg.mp (Module.Finite.of_surjective _ hsurj)

theorem exists_smul_mem_of_localized'_le {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Module A W] [IsScalarTower R A W] (g : V →ₗ[R] W) [IsLocalizedModule S g] {N₁ N₂ : Submodule R V}
    (hfg : N₁.FG) (h : N₁.localized' A S g ≤ N₂.localized' A S g) :
    ∃ u : S, ∀ x ∈ N₁, (u : R) • x ∈ N₂ := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have key : ∀ x ∈ (s : Set V), ∃ u : S, (u : R) • x ∈ N₂ := by
    intro x hx
    have hx1 : g x ∈ (Submodule.span R (s : Set V)).localized' A S g :=
      ⟨x, Submodule.subset_span hx, 1, IsLocalizedModule.mk'_one S g x⟩
    obtain ⟨y, hy, t, hyt⟩ := h hx1
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul, eq_comm, ← sub_eq_zero, ← map_sub,
      IsLocalizedModule.eq_zero_iff S g] at hyt
    obtain ⟨t', ht'⟩ := hyt
    refine ⟨t' * t, ?_⟩
    rw [Submonoid.smul_def, smul_sub, sub_eq_zero, smul_smul] at ht'
    rw [Submonoid.coe_mul, ht']
    exact N₂.smul_mem _ hy
  choose u hu using key
  refine ⟨∏ x ∈ s.attach, u x.1 x.2, ?_⟩
  have hgen : ∀ x (hx : x ∈ s), ((∏ x ∈ s.attach, u x.1 x.2 : S) : R) • x ∈ N₂ := by
    intro x hx
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_attach s ⟨x, hx⟩), Submonoid.coe_mul, mul_smul]
    exact N₂.smul_mem _ (hu x hx)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => rw [smul_zero]; exact N₂.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact N₂.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N₂.smul_mem a hx

section CD

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
  {B : Type} [CommRing B] [Algebra 𝒪 B] (M : FullLattice 𝒪 K₀)

scoped instance finite_lattice : Module.Finite 𝒪 (↥M.1) := Module.Finite.iff_fg.mpr M.2.1

theorem rTensor_smul_left' {C : Type} [CommRing C] [Algebra 𝒪 C] (φ : B →ₐ[𝒪] C) (b : B)
    (x : latticeBaseChange 𝒪 K₀ B M) :
    LinearMap.rTensor (↥M.1) φ.toLinearMap (b • x) = φ b • LinearMap.rTensor (↥M.1) φ.toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul b' v =>
    rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul',
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul, smul_eq_mul, map_mul]

theorem lineBaseChange_le_of_smul_mem {C : Type} [CommRing C] [Algebra 𝒪 C] (φ : B →ₐ[𝒪] C)
    {N₁ N₂ : Submodule B (latticeBaseChange 𝒪 K₀ B M)} (u : B) (hu : IsUnit (φ u))
    (h : ∀ x ∈ N₁, u • x ∈ N₂) : lineBaseChange φ M N₁ ≤ lineBaseChange φ M N₂ := by
  rw [lineBaseChange, lineBaseChange]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc⟩ := hu
  have e : LinearMap.rTensor (↥M.1) φ.toLinearMap x =
      (c⁻¹ : Cˣ) • LinearMap.rTensor (↥M.1) φ.toLinearMap (u • x) := by
    rw [rTensor_smul_left' M φ u x, ← hc, ← Units.smul_def, inv_smul_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u • x, h x hx, rfl⟩)

noncomputable abbrev bc (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] :
    latticeBaseChange 𝒪 K₀ B M →ₗ[B] latticeBaseChange 𝒪 K₀ C M :=
  TensorProduct.AlgebraTensorModule.rTensor 𝒪 (↥M.1) (Algebra.linearMap B C)

theorem bc_apply (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
    (x : latticeBaseChange 𝒪 K₀ B M) :
    bc M C x = LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 B C).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b v =>
    simp only [bc, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
      TensorProduct.AlgebraTensorModule.rTensor_tmul, Algebra.linearMap_apply]

theorem lineBaseChange_eq_localized' (S : Submonoid B) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C]
    [IsScalarTower 𝒪 B C] [IsLocalization S C] (N : Submodule B (latticeBaseChange 𝒪 K₀ B M)) :
    lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N = N.localized' C S (bc M C) := by
  rw [Submodule.localized'_eq_span, lineBaseChange]
  exact congrArg (Submodule.span C) (Set.image_congr fun x _ => (bc_apply M C x).symm)

end CD

end SpreadGC9
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq.SpreadGC9"

open SpreadGC9 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (M : FullLattice 𝒪 K₀)
    (N₁ N₂ : Submodule B (latticeBaseChange 𝒪 K₀ B M))
    (h₁ : Module.Invertible B (latticeBaseChange 𝒪 K₀ B M ⧸ N₁))
    (h₂ : Module.Invertible B (latticeBaseChange 𝒪 K₀ B M ⧸ N₂))
    (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (Localization.AtPrime 𝔭)) M N₁ =
      lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (Localization.AtPrime 𝔭)) M N₂) :
    ∃ f : B, f ∉ 𝔭 ∧
      ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away f C],
        lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₁ = lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₂ := by
  haveI := h₁; haveI := h₂
  have hfg₁ : N₁.FG := fg_of_projective_quotient N₁
  have hfg₂ : N₂.FG := fg_of_projective_quotient N₂
  rw [lineBaseChange_eq_localized' M 𝔭.primeCompl, lineBaseChange_eq_localized' M 𝔭.primeCompl] at h
  obtain ⟨u₁, hu₁⟩ := exists_smul_mem_of_localized'_le 𝔭.primeCompl (Localization.AtPrime 𝔭)
    (bc M (Localization.AtPrime 𝔭)) hfg₁ h.le
  obtain ⟨u₂, hu₂⟩ := exists_smul_mem_of_localized'_le 𝔭.primeCompl (Localization.AtPrime 𝔭)
    (bc M (Localization.AtPrime 𝔭)) hfg₂ h.ge
  refine ⟨u₁ * u₂, (𝔭.primeCompl.mul_mem u₁.2 u₂.2 : (u₁ : B) * u₂ ∈ 𝔭.primeCompl), ?_⟩
  intro C _ _ _ _ _
  have hu : IsUnit ((IsScalarTower.toAlgHom 𝒪 B C) ((u₁ : B) * u₂)) := by
    rw [IsScalarTower.coe_toAlgHom']
    exact IsLocalization.Away.algebraMap_isUnit ((u₁ : B) * u₂)
  rw [map_mul] at hu
  exact le_antisymm (lineBaseChange_le_of_smul_mem M _ u₁ (isUnit_of_mul_isUnit_left hu) hu₁)
    (lineBaseChange_le_of_smul_mem M _ u₂ (isUnit_of_mul_isUnit_right hu) hu₂)

end S_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq (solution)
