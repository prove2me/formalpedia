-- Prove2me | solution 1 for CerednikDrinfeld.QM.existsUnique_linearMap_forall_eq_pushPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9e6d0fd7-37da-595c-ac3c-9efddb52d233

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

namespace DiffExists

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
  (g : A ⟶ A) (hg : g ≫ f = f)
  (hg_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
    pushPt g hg (L.mul t P Q) = L.mul t (pushPt g hg P) (pushPt g hg Q))

include hg_hom in

theorem pushPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) :
    pushPt g hg (L.one t) = L.one t := by
  letI := L.pointGroup t
  have h := hg_hom t (L.one t) (L.one t)
  rw [L.one_mul] at h

  have h' : pushPt g hg (L.one t) * pushPt g hg (L.one t) = pushPt g hg (L.one t) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h'

include hg_hom in

theorem isTangentVector_pushPt (k : Type) [Field k] (sk : B →+* k)
    (P : SchemeHomOver (tangentBase k sk) f) (hP : IsTangentVector L k sk P) :
    IsTangentVector L k sk (pushPt g hg P) := by
  unfold IsTangentVector at hP ⊢
  rw [mapPt_coe, ← Category.assoc, hP, ← mapPt_coe g hg (L.one (geomPoint k sk))]
  exact congrArg Subtype.val (pushPt_one L g hg hg_hom (geomPoint k sk))

end DiffExists

theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k)
    (V : Type) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (g : A ⟶ A) (hg : g ≫ f = f)
    (hg_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      pushPt g hg (L.mul t P Q) = L.mul t (pushPt g hg P) (pushPt g hg Q)) :
    ∃! Φ : V →ₗ[k] V, ∀ v : V, τ (Φ v) = pushPt g hg (τ v) := by

  have hmem : ∀ v : V, pushPt g hg (τ v) ∈ Set.range τ := fun v =>
    (hrange _).2 (DiffExists.isTangentVector_pushPt L g hg hg_hom k sk (τ v) ((hrange _).1 ⟨v, rfl⟩))
  let Φf : V → V := fun v => Classical.choose (hmem v)
  have hΦf : ∀ v, τ (Φf v) = pushPt g hg (τ v) := fun v => Classical.choose_spec (hmem v)
  have hΦ_add : ∀ v w, Φf (v + w) = Φf v + Φf w := fun v w => hinj (by
    rw [hΦf, hadd, hg_hom, ← hΦf, ← hΦf, ← hadd])
  have hΦf' : ∀ v, (τ (Φf v)).1 = (τ v).1 ≫ g := fun v => by rw [hΦf]; rfl
  have hΦ_smul : ∀ (c : k) (v : V), Φf (c • v) = c • Φf v := fun c v => hinj (Subtype.ext (by
    rw [hΦf', hsmul, Category.assoc, ← hΦf', ← hsmul]))
  refine ⟨{ toFun := Φf, map_add' := hΦ_add, map_smul' := hΦ_smul }, hΦf, ?_⟩
  intro Ψ hΨ
  refine LinearMap.ext fun v => hinj ?_
  rw [hΨ v]
  exact (hΦf v).symm

end S_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt
end P2MW
export P2MW.S_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt (solution)
