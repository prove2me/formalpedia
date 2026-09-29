-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelOne_extraLevel_and_exists_of_extraLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/77880486-f0b1-53b4-9812-9e1f9afe9455

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel.CerednikDrinfeld.QM"
open scoped Quaternion TensorProduct NumberField

universe u

namespace CerednikDrinfeld
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt pushPt FactorsThrough nsmulPt geomPoint FakeEllipticCurve"
namespace LevelDictAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem mapPt_id {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (h : 𝟙 A ≫ f = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (𝟙 A) h P = P :=
  Subtype.ext (Category.comp_id _)

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) (hx : L.mul t x x = x) :
    x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [hx]
    _ = L.one t := L.inv_mul_cancel t x

theorem inv_one {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : L.inv t (L.one t) = L.one t := by
  have := L.inv_mul_cancel t (L.one t)
  rwa [L.mul_one] at this

theorem nsmulPt_one {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : ∀ n : ℕ, nsmulPt L t n (L.one t) = L.one t
  | 0 => rfl
  | n + 1 => by
    show L.mul t (nsmulPt L t n (L.one t)) (L.one t) = L.one t
    rw [nsmulPt_one L t n, L.one_mul]

theorem pushPt_act_one (E : FakeEllipticCurve Λ N S) (x : ↥Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
  apply eq_one_of_mul_self
  have h := E.act_hom x t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  exact h.symm

@[reducible] noncomputable def unitSection (E : FakeEllipticCurve Λ N S) : Spec (CommRingCat.of S) ⟶ E.A :=
  (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem unitSection_comp (E : FakeEllipticCurve Λ N S) : unitSection E ≫ E.f = 𝟙 _ :=
  (E.L.one (𝟙 (Spec (CommRingCat.of S)))).2

theorem factorsThrough_unitSection_iff (E : FakeEllipticCurve Λ N S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    FactorsThrough (unitSection E) P ↔ P = E.L.one t := by
  have hnat : (E.L.one t).1 = t ≫ unitSection E := by
    have := E.L.one_natural (𝟙 (Spec (CommRingCat.of S))) t t (Category.comp_id t)
    rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]
  constructor
  · rintro ⟨P₀, hP₀⟩
    have hP₀t : P₀ = t := by
      have := congrArg (· ≫ E.f) hP₀
      simp only [Category.assoc, unitSection_comp, Category.comp_id] at this
      rw [this, P.2]
    apply Subtype.ext
    rw [hnat, ← hP₀, hP₀t]
  · rintro rfl
    exact ⟨t, hnat.symm⟩

@[reducible] noncomputable def toLevelOne (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve Λ 1 S where
  A := E.A
  f := E.f
  L := E.L
  comm := E.comm
  bundle := E.bundle
  dim_fibre := E.dim_fibre
  act := E.act
  act_over := E.act_over
  act_hom := E.act_hom
  act_one := E.act_one
  act_mul := E.act_mul
  act_add := E.act_add
  act_trace := E.act_trace
  C := Spec (CommRingCat.of S)
  lev := unitSection E
  lev_closed := by
    haveI : IsProper E.f := E.bundle.proper
    haveI : IsClosedImmersion (unitSection E ≫ E.f) := by
      rw [unitSection_comp]; infer_instance
    exact IsClosedImmersion.of_comp (unitSection E) E.f
  lev_sub := by
    intro T t P Q hP hQ
    rw [factorsThrough_unitSection_iff] at hP hQ ⊢
    rw [factorsThrough_unitSection_iff]
    subst hP; subst hQ
    exact ⟨E.L.one_mul t _, inv_one E.L t⟩
  lev_one := fun t => (factorsThrough_unitSection_iff E t _).2 rfl
  lev_torsion := by
    intro T t P hP
    rw [factorsThrough_unitSection_iff] at hP
    subst hP
    exact nsmulPt_one E.L t 1
  lev_stable := by
    intro x T t P hP
    rw [factorsThrough_unitSection_iff] at hP ⊢
    subst hP
    exact pushPt_act_one E x t
  lev_finite := by rw [unitSection_comp]; infer_instance
  lev_flat := by rw [unitSection_comp]; infer_instance
  lev_finitePresentation := by rw [unitSection_comp]; infer_instance
  lev_rank := by
    intro s
    rw [unitSection_comp, Scheme.Hom.finrank_eq_one_of_isIso]
    simp
  lev_fibre := by
    intro k _ _ sk _
    haveI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff).2 rfl
    haveI : Unique (ZMod 1 × ZMod 1) := uniqueOfSubsingleton (0, 0)
    haveI : Unique {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (unitSection E) P} :=
      { default := ⟨E.L.one _, (factorsThrough_unitSection_iff E _ _).2 rfl⟩
        uniq := fun P => Subtype.ext ((factorsThrough_unitSection_iff E _ _).1 P.2) }
    refine ⟨Equiv.ofUnique _ _, fun x y => ?_⟩
    have h1 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ (x + y) :
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (unitSection E) P}) :
          SchemeHomOver (geomPoint k sk) E.f) = E.L.one _ :=
      (factorsThrough_unitSection_iff E _ _).1 (Subtype.prop _)
    have h2 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ x :
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (unitSection E) P}) :
          SchemeHomOver (geomPoint k sk) E.f) = E.L.one _ :=
      (factorsThrough_unitSection_iff E _ _).1 (Subtype.prop _)
    have h3 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ y :
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (unitSection E) P}) :
          SchemeHomOver (geomPoint k sk) E.f) = E.L.one _ :=
      (factorsThrough_unitSection_iff E _ _).1 (Subtype.prop _)
    rw [h1, h2, h3, E.L.one_mul]

@[reducible] noncomputable def toExtraLevel (E : FakeEllipticCurve Λ N S) : (toLevelOne E).ExtraLevel N where
  K := E.C
  levK := E.lev
  levK_closed := E.lev_closed
  levK_sub := E.lev_sub
  levK_one := E.lev_one
  levK_torsion := E.lev_torsion
  levK_stable := E.lev_stable
  levK_disjoint := fun t P _ hP => (factorsThrough_unitSection_iff E t P).1 hP
  levK_finite := E.lev_finite
  levK_flat := E.lev_flat
  levK_finitePresentation := E.lev_finitePresentation
  levK_rank := E.lev_rank
  levK_fibre := E.lev_fibre

@[reducible] noncomputable def ofExtraLevel (E₁ : FakeEllipticCurve Λ 1 S) (K : E₁.ExtraLevel N) : FakeEllipticCurve Λ N S where
  A := E₁.A
  f := E₁.f
  L := E₁.L
  comm := E₁.comm
  bundle := E₁.bundle
  dim_fibre := E₁.dim_fibre
  act := E₁.act
  act_over := E₁.act_over
  act_hom := E₁.act_hom
  act_one := E₁.act_one
  act_mul := E₁.act_mul
  act_add := E₁.act_add
  act_trace := E₁.act_trace
  C := K.K
  lev := K.levK
  lev_closed := K.levK_closed
  lev_sub := K.levK_sub
  lev_one := K.levK_one
  lev_torsion := K.levK_torsion
  lev_stable := K.levK_stable
  lev_finite := K.levK_finite
  lev_flat := K.levK_flat
  lev_finitePresentation := K.levK_finitePresentation
  lev_rank := K.levK_rank
  lev_fibre := K.levK_fibre

end CerednikDrinfeld.QM.LevelDictAux

open CerednikDrinfeld.QM.LevelDictAux in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (S : Type u) [CommRing S] :
    (∀ E : FakeEllipticCurve Λ N S,
      ∃ (E₁ : FakeEllipticCurve Λ 1 S) (K : E₁.ExtraLevel N) (e : E.A ≅ E₁.A) (he : e.hom ≫ E₁.f = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E₁.act x) ∧
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough K.levK (mapPt e.hom he P))) ∧
    (∀ (E₁ : FakeEllipticCurve Λ 1 S) (K : E₁.ExtraLevel N),
      ∃ (E : FakeEllipticCurve Λ N S) (e : E.A ≅ E₁.A) (he : e.hom ≫ E₁.f = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E₁.act x) ∧
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough K.levK (mapPt e.hom he P))) := by
  refine ⟨fun E => ?_, fun E₁ K => ?_⟩
  · refine ⟨toLevelOne E, toExtraLevel E, Iso.refl _, Category.id_comp _, ?_, ?_, ?_⟩
    · intro T t P Q
      simp only [Iso.refl_hom, mapPt_id]
    · intro x
      simp
    · intro T t P
      simp only [Iso.refl_hom, mapPt_id]
  · refine ⟨ofExtraLevel E₁ K, Iso.refl _, Category.id_comp _, ?_, ?_, ?_⟩
    · intro T t P Q
      simp only [Iso.refl_hom, mapPt_id]
    · intro x
      simp
    · intro T t P
      simp only [Iso.refl_hom, mapPt_id]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel (solution)
