-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_moduleEnd_apply_eq_pushPt_of_isTangentVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/245782b6-8eaf-5830-afce-454ce089c8b4

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace TangentActPf

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem push_one_eq (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt φ hφ (L.one t) = L.one t := by
  set e := pushPt φ hφ (L.one t) with he
  have hx : L.mul t e e = e := by rw [he, ← hhom, L.one_mul]
  calc e = L.mul t (L.one t) e := (L.one_mul _ _).symm
    _ = L.mul t (L.mul t (L.inv t e) e) e := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t e) (L.mul t e e) := L.mul_assoc _ _ _ _
    _ = L.mul t (L.inv t e) e := by rw [hx]
    _ = L.one t := L.inv_mul_cancel _ _

theorem pushPt_comp (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) (hφψ : (φ ≫ ψ) ≫ f = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    pushPt (φ ≫ ψ) hφψ P = pushPt ψ hψ (pushPt φ hφ P) := by
  apply Subtype.ext
  simp [pushPt, mapPt, Category.assoc]

theorem pushPt_id {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (h : 𝟙 A ≫ f = f) (P : SchemeHomOver t f) :
    pushPt (𝟙 A) h P = P := by
  apply Subtype.ext
  simp [pushPt, mapPt]

end TangentActPf

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (k : Type u) [Field k] (sk : S →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    ∃ θ : ↥Λ → Module.End k V,
      (∀ (x : ↥Λ) (v : V), τ (θ x v) = pushPt (act x) (act_over x) (τ v)) ∧
      (∀ x y : ↥Λ, θ (x + y) = θ x + θ y) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = θ x * θ y) ∧
      (∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) → θ m = Φ) := by
  classical

  have hunit : ∀ x : ↥Λ, pushPt (act x) (act_over x) (L.one (geomPoint k sk)) = L.one (geomPoint k sk) :=
    fun x => TangentActPf.push_one_eq L (act x) (act_over x) (act_hom x) _
  have htv : ∀ (x : ↥Λ) (v : V), IsTangentVector L k sk (pushPt (act x) (act_over x) (τ v)) := by
    intro x v
    have hv : IsTangentVector L k sk (τ v) := (hrange (τ v)).mp ⟨v, rfl⟩
    change tangentZero k ≫ ((τ v).1 ≫ act x) = (L.one (geomPoint k sk)).1
    rw [← Category.assoc, show tangentZero k ≫ (τ v).1 = _ from hv]
    exact congrArg Subtype.val (hunit x)
  have hex : ∀ (x : ↥Λ) (v : V), ∃ w : V, τ w = pushPt (act x) (act_over x) (τ v) :=
    fun x v => (hrange _).mpr (htv x v)
  choose θv hθv using hex

  have hθadd : ∀ (x : ↥Λ) (v w : V), θv x (v + w) = θv x v + θv x w := by
    intro x v w
    apply hinj
    rw [hθv, hadd, hadd, act_hom, hθv, hθv]
  have hθsmul : ∀ (x : ↥Λ) (c : k) (v : V), θv x (c • v) = c • θv x v := by
    intro x c v
    apply hinj
    apply Subtype.ext
    rw [hsmul, congrArg Subtype.val (hθv x (c • v)), congrArg Subtype.val (hθv x v)]
    change (τ (c • v)).1 ≫ act x = tangentScale k c ≫ ((τ v).1 ≫ act x)
    rw [hsmul, Category.assoc]
  let θ : ↥Λ → Module.End k V := fun x =>
    { toFun := θv x, map_add' := hθadd x, map_smul' := hθsmul x }
  have hθ : ∀ (x : ↥Λ) (v : V), τ (θ x v) = pushPt (act x) (act_over x) (τ v) := fun x v => hθv x v
  refine ⟨θ, hθ, ?_, ?_, ?_, ?_⟩
  ·
    intro x y
    apply LinearMap.ext; intro v
    apply hinj
    rw [hθ, act_add, LinearMap.add_apply, hadd, hθ, hθ]
  ·
    intro h
    apply LinearMap.ext; intro v
    apply hinj
    rw [hθ, Module.End.one_apply]
    apply Subtype.ext
    change (τ v).1 ≫ act ⟨1, h⟩ = (τ v).1
    rw [act_one h, Category.comp_id]
  ·
    intro x y h
    apply LinearMap.ext; intro v
    apply hinj
    rw [hθ, Module.End.mul_apply, hθ, hθ]
    apply Subtype.ext
    change (τ v).1 ≫ act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ((τ v).1 ≫ act y) ≫ act x
    rw [act_mul x y h, Category.assoc]
  ·
    intro m Φ hΦ
    apply LinearMap.ext; intro v
    apply hinj
    rw [hθ, hΦ]

end S_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector (solution)
