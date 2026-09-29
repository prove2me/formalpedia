-- Prove2me | solution 1 for CerednikDrinfeld.QM.isTangentVector_specMap_fromSpec_iff_pointDerivations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0847a50c-c821-5981-9a19-f4fc4cf2d6a6

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_isTangentVector_specMap_fromSpec_iff_pointDerivations

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace DerTangentS2a

section Plumbing

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem appLE_specMap_fromSpec {S : CommRingCat.{u}} (θ : Γ(X, U) ⟶ S)
    (h : ⊤ ≤ (Spec.map θ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map θ ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso S).hom = θ := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [IsAffineOpen.fromSpec_preimage_self]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map θ) hU.fromSpec U ⊤ ⊤ h1 le_top]
  have h2 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    rfl
  have h3 : (Spec.map θ).appLE ⊤ ⊤ le_top = (Spec.map θ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h2, h3, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem le_preimage_specMap_fromSpec {S : CommRingCat.{u}} (θ : Γ(X, U) ⟶ S) :
    ⊤ ≤ (Spec.map θ ≫ hU.fromSpec) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
  exact le_top

end Plumbing

section RingMap

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A] (ev : A →+* K)
  (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
  (D : ↥(Algebra.PointDerivations K A ev M))

def θ : A →+* TrivSqZeroExt K M where
  toFun r := TrivSqZeroExt.inl (ev r) + TrivSqZeroExt.inr (D.1 r)
  map_one' := by
    apply TrivSqZeroExt.ext <;>
      simp [Algebra.PointDerivations.apply_one D.2]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul]
      rw [Algebra.PointDerivations.apply_mul D.2 a b, op_smul_eq_smul, add_comm]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext <;> simp [add_add_add_comm]

@[scoped simp] theorem θ_apply (r : A) : θ ev M D r = TrivSqZeroExt.inl (ev r) + TrivSqZeroExt.inr (D.1 r) := rfl

theorem fst_θ (r : A) : (θ ev M D r).fst = ev r := by simp

theorem fstHom_comp_θ : (TrivSqZeroExt.fstHom K K M).toRingHom.comp (θ ev M D) = ev := by
  ext r; exact fst_θ ev M D r

theorem θ_comp_algebraMap (hev : ∀ c : K, ev (algebraMap K A c) = c) :
    (θ ev M D).comp (algebraMap K A) = algebraMap K (TrivSqZeroExt K M) := by
  ext c
  · simp [hev, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [Algebra.PointDerivations.apply_algebraMap D.2, TrivSqZeroExt.algebraMap_eq_inl]

end RingMap

end DerTangentS2a
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_isTangentVector_specMap_fromSpec_iff_pointDerivations.DerTangentS2a"

open DerTangentS2a

theorem solution
    (κ : Type) [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ fX)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of κ) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι = (L.one (𝟙 _)).1) :
    letI := algebraOfHom fX U

    (∀ (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ)) (χ : Γ(X, U) →+* DualNumber κ),
        (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
        (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) →
        ∃ h : (Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec) ≫ fX = tangentBase κ (RingHom.id κ),
          IsTangentVector L κ (RingHom.id κ) ⟨Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec, h⟩) ∧

    (∀ P : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX, IsTangentVector L κ (RingHom.id κ) P →
        ∃ (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ)) (χ : Γ(X, U) →+* DualNumber κ),
          (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) ∧
          (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) ∧
          P.1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec) ∧

    (∀ χ χ' : Γ(X, U) →+* DualNumber κ,
        Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom χ') ≫ hU.fromSpec → χ = χ') := by
  letI : Algebra κ Γ(X, U) := algebraOfHom fX U
  set ev : Γ(X, U) →+* κ := (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom with hevdef

  have heP : e₁ ≫ U.ι ≫ fX = 𝟙 _ := by rw [← Category.assoc, he₁]; exact (L.one (𝟙 _)).2

  have hfx : hU.fromSpec ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap κ Γ(X, U))) := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec fX (isAffineOpen_top _) hU (le_top : U ≤ fX ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
    exact this.symm

  have hfactor : ∀ {S : CommRingCat.{0}} (p : Spec S ⟶ X) (hp : ⊤ ≤ p ⁻¹ᵁ U),
      p = Spec.map (p.appLE U ⊤ hp ≫ (Scheme.ΓSpecIso S).hom) ≫ hU.fromSpec := by
    intro S p hp
    have := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top _) hp
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]

  have hι : ⊤ ≤ (e₁ ≫ U.ι) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
    exact le_top
  have happ : (e₁ ≫ U.ι).appLE U ⊤ hι = U.topIso.inv ≫ e₁.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE e₁ U.ι U ⊤ ⊤ (by rw [Scheme.Opens.ι_preimage_self]) le_top]
    congr 1
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hev_hom : CommRingCat.ofHom ev = (e₁ ≫ U.ι).appLE U ⊤ hι ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom := by
    rw [happ, Category.assoc, hevdef]; rfl
  have hePι' : e₁ ≫ U.ι = Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec := by rw [hev_hom]; exact hfactor _ hι

  have hev : ∀ c : κ, ev (algebraMap κ Γ(X, U) c) = c := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap κ Γ(X, U)) ≫ CommRingCat.ofHom ev) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, Spec.map_id, ← hfx, ← Category.assoc, ← hePι', Category.assoc, heP]
    have h2 := Spec.map_injective h1
    intro c
    have := congrArg (fun f : CommRingCat.of κ ⟶ CommRingCat.of κ => f.hom c) h2
    simpa using this

  have hinjR : ∀ {R : Type} [CommRing R] (χ χ' : Γ(X, U) →+* R),
      Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom χ') ≫ hU.fromSpec → χ = χ' := by
    intro R _ χ χ' h
    have h' := Spec.map_injective ((cancel_mono hU.fromSpec).mp h)
    exact congrArg CommRingCat.Hom.hom h'

  have hgeom : geomPoint κ (RingHom.id κ) = 𝟙 (Spec (CommRingCat.of κ)) := by
    show Spec.map (CommRingCat.ofHom (RingHom.id κ)) = 𝟙 _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have hone_geom : (L.one (geomPoint κ (RingHom.id κ))).1 = (L.one (𝟙 _)).1 := by
    have : ∀ (t t' : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of κ)) (h : t = t'), (L.one t).1 = (L.one t').1 := by
      intro t t' h; subst h; rfl
    exact this _ _ hgeom

  have hpt : ∀ x y : ↥(Spec (CommRingCat.of (DualNumber κ))), x = y := by
    have key : ∀ z : ↥(Spec (CommRingCat.of (DualNumber κ))), z.asIdeal = IsLocalRing.maximalIdeal (DualNumber κ) := by
      intro z
      have hε : (DualNumber.eps : DualNumber κ) ∈ z.asIdeal := by
        obtain ⟨n, hn⟩ := (DualNumber.isNilpotent_eps : IsNilpotent (DualNumber.eps : DualNumber κ))
        exact z.2.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
      have hle : IsLocalRing.maximalIdeal (DualNumber κ) ≤ z.asIdeal := by
        rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_le, Set.singleton_subset_iff]
        exact hε
      exact ((IsLocalRing.maximalIdeal.isMaximal (DualNumber κ)).eq_of_le z.2.ne_top hle).symm
    intro x y
    exact PrimeSpectrum.ext ((key x).trans (key y).symm)
  refine ⟨?_, ?_, fun χ χ' h => hinjR χ χ' h⟩
  ·
    intro δ χ hχ1 hχ2
    have hχ : χ = θ ev κ δ := by
      apply RingHom.ext; intro a
      apply TrivSqZeroExt.ext
      · rw [hχ1 a, fst_θ]
      · rw [hχ2 a]; simp
    have hover : (Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec) ≫ fX = tangentBase κ (RingHom.id κ) := by
      rw [Category.assoc, hfx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ, θ_comp_algebraMap ev κ δ hev]
      rfl
    refine ⟨hover, ?_⟩
    show tangentZero κ ≫ Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec = (L.one (geomPoint κ (RingHom.id κ))).1
    rw [hone_geom, ← he₁, hePι', ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ Spec.map (CommRingCat.ofHom χ) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ, fstHom_comp_θ]
  ·
    intro P hP
    have hP' : tangentZero κ ≫ P.1 = e₁ ≫ U.ι := by
      rw [show tangentZero κ ≫ P.1 = (L.one (geomPoint κ (RingHom.id κ))).1 from hP, hone_geom, he₁]

    have hsub : ⊤ ≤ P.1 ⁻¹ᵁ U := by
      intro x _
      show P.1.base x ∈ (U : Set X)
      rw [hpt x ((tangentZero κ).base (IsLocalRing.closedPoint κ))]
      change (tangentZero κ ≫ P.1) (IsLocalRing.closedPoint κ) ∈ (U : Set X)
      rw [hP']
      exact (e₁ (IsLocalRing.closedPoint κ)).2
    let χ : Γ(X, U) →+* DualNumber κ := (P.1.appLE U ⊤ hsub ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber κ))).hom).hom
    have hPχ : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec := hfactor P.1 hsub

    have hχalg : χ.comp (algebraMap κ Γ(X, U)) = algebraMap κ (DualNumber κ) := by
      have h1 : Spec.map (CommRingCat.ofHom (χ.comp (algebraMap κ Γ(X, U)))) = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hfx, ← Category.assoc, ← hPχ, P.2]
        rfl
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

    have hχfst : (TrivSqZeroExt.fstHom κ κ κ).toRingHom.comp χ = ev := by
      apply hinjR
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← hPχ, ← hePι']
      exact hP'
    have hfst : ∀ a, TrivSqZeroExt.fst (χ a) = ev a := fun a => congrArg (fun f : Γ(X, U) →+* κ => f a) hχfst
    have hinl : ∀ c : κ, χ (algebraMap κ Γ(X, U) c) = TrivSqZeroExt.inl c := fun c => by
      rw [← RingHom.comp_apply, hχalg, TrivSqZeroExt.algebraMap_eq_inl]

    let δ₀ : Γ(X, U) →ₗ[κ] κ :=
      { toFun := fun a => TrivSqZeroExt.snd (χ a)
        map_add' := fun a b => by simp [map_add]
        map_smul' := fun c a => by
          rw [Algebra.smul_def, map_mul, hinl, TrivSqZeroExt.snd_mul]
          simp }
    have hδ₀ : δ₀ ∈ Algebra.PointDerivations κ Γ(X, U) ev κ := by
      intro a b
      show TrivSqZeroExt.snd (χ (a * b)) = ev a • TrivSqZeroExt.snd (χ b) + ev b • TrivSqZeroExt.snd (χ a)
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
    refine ⟨⟨δ₀, hδ₀⟩, χ, hfst, fun a => rfl, hPχ⟩

end S_CerednikDrinfeld_QM_isTangentVector_specMap_fromSpec_iff_pointDerivations
end P2MW
export P2MW.S_CerednikDrinfeld_QM_isTangentVector_specMap_fromSpec_iff_pointDerivations (solution)
