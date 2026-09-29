-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/65961fd3-38c5-5d5c-a179-1db92271dca5

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback.CerednikDrinfeld.QM"
open scoped Quaternion

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt pushPt FactorsThrough nsmulPt geomPoint FakeEllipticCurve"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "ExtraLevel WithExtraLevel IsLevelIsogeny IsPullback A f act L C lev act_over"
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

section QRScaffold

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'} {ℓ : ℕ}
  (u : WithExtraLevel Λ N ℓ S) (Ā : FakeEllipticCurve Λ N S')
  (g : Ā.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g Ā.f u.1.f (Spec.map (CommRingCat.ofHom φ)))

noncomputable def Kbar : Scheme.{u} := pullback u.2.levK g

noncomputable def levKbar : Kbar u Ā g ⟶ Ā.A := pullback.snd u.2.levK g

noncomputable def Kbar.pr : Kbar u Ā g ⟶ u.2.K := pullback.fst u.2.levK g

omit hg in
theorem Kbar.condition : Kbar.pr u Ā g ≫ u.2.levK = levKbar u Ā g ≫ g := pullback.condition

omit hg in
theorem isPullback_small : CategoryTheory.IsPullback (Kbar.pr u Ā g) (levKbar u Ā g) u.2.levK g := CategoryTheory.IsPullback.of_hasPullback _ _

include hg in

theorem isPullback_big :
    CategoryTheory.IsPullback (Kbar.pr u Ā g) (levKbar u Ā g ≫ Ā.f) (u.2.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_small u Ā g).paste_vert hg

omit hg in
theorem levKbar_closed : IsClosedImmersion (levKbar u Ā g) := by
  haveI := u.2.levK_closed
  exact MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance

include hg in
theorem levKbar_finite : IsFinite (levKbar u Ā g ≫ Ā.f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) (isPullback_big u Ā g hg) u.2.levK_finite

include hg in
theorem levKbar_flat : Flat (levKbar u Ā g ≫ Ā.f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) (isPullback_big u Ā g hg) u.2.levK_flat

include hg in
theorem levKbar_finitePresentation : LocallyOfFinitePresentation (levKbar u Ā g ≫ Ā.f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation)
    (isPullback_big u Ā g hg) u.2.levK_finitePresentation

include hg in
theorem levKbar_rank (s : ↥(Spec (CommRingCat.of S'))) : (levKbar u Ā g ≫ Ā.f).finrank s = ℓ ^ 2 := by
  haveI := u.2.levK_flat
  haveI := u.2.levK_finite
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_big u Ā g hg)]
  exact u.2.levK_rank _

omit hg in

theorem factorsThrough_levKbar_iff {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' Ā.f) :
    FactorsThrough (levKbar u Ā g) P ↔ ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g := by
  constructor
  · rintro ⟨P₁, hP₁⟩
    refine ⟨P₁ ≫ Kbar.pr u Ā g, ?_⟩
    rw [Category.assoc, Kbar.condition, ← Category.assoc, hP₁]
  · rintro ⟨P₀, hP₀⟩
    exact ⟨pullback.lift P₀ P.1 hP₀, pullback.lift_snd _ _ _⟩

end QRScaffold

end CerednikDrinfeld.QM.FakeEllipticCurve

section BC

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S')} {fY : Y ⟶ Spec (CommRingCat.of S)}
  (g : X ⟶ Y) (sq : CategoryTheory.IsPullback g fX fY (Spec.map (CommRingCat.ofHom φ)))

def bc {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' fX) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) fY :=
  ⟨P.1 ≫ g, by rw [Category.assoc, sq.w, ← Category.assoc, P.2]⟩

theorem bc_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' fX) :
    (bc g sq P).1 = P.1 ≫ g := rfl

theorem bc_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' fX}
    (h : bc g sq P = bc g sq Q) : P = Q := by
  apply Subtype.ext
  apply sq.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

variable (LX : RelativeGroupLaw S' fX) (LY : RelativeGroupLaw S fY)
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' fX),
    (LX.mul t' P Q).1 ≫ g = (LY.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (bc g sq P) (bc g sq Q)).1)

include hmul in
theorem bc_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' fX) :
    bc g sq (LX.mul t' P Q) = LY.mul _ (bc g sq P) (bc g sq Q) := Subtype.ext (hmul t' P Q)

include hmul in
theorem bc_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) : bc g sq (LX.one t') = LY.one _ := by
  have h := bc_mul g sq LX LY hmul t' (LX.one t') (LX.one t')
  rw [LX.one_mul] at h

  have h2 := congrArg (fun z => LY.mul _ (LY.inv _ (bc g sq (LX.one t'))) z) h
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at h2
  exact h2.symm

include hmul in
theorem bc_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' fX) :
    bc g sq (LX.inv t' P) = LY.inv _ (bc g sq P) := by
  have h := bc_mul g sq LX LY hmul t' (LX.inv t' P) P
  rw [LX.inv_mul_cancel, bc_one g sq LX LY hmul] at h

  have h2 := congrArg (fun z => LY.mul _ z (LY.inv _ (bc g sq P))) h
  rw [LY.one_mul, LY.mul_assoc, RelativeGroupLaw.mul_inv_cancel, LY.mul_one] at h2
  exact h2.symm

include hmul in
theorem bc_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (P : SchemeHomOver t' fX) :
    bc g sq (nsmulPt LX t' n P) = nsmulPt LY _ n (bc g sq P) := by
  induction n with
  | zero => exact bc_one g sq LX LY hmul t'
  | succ n ih =>
    show bc g sq (LX.mul t' (nsmulPt LX t' n P) P) = LY.mul _ (nsmulPt LY _ n (bc g sq P)) (bc g sq P)
    rw [bc_mul g sq LX LY hmul, ih]

omit sq in

theorem factorsThrough_of_val_eq {C : Scheme.{u}} (lev : C ⟶ Y) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t₁ fY) (Q : SchemeHomOver t₂ fY) (h : P.1 = Q.1) :
    FactorsThrough lev P → FactorsThrough lev Q := by
  rintro ⟨P₀, hP₀⟩; exact ⟨P₀, hP₀.trans h⟩

end BC

section BaseEq
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem QRAux.mul_val_congr {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst h
  have hP' : P = P' := Subtype.ext hP
  have hQ' : Q = Q' := Subtype.ext hQ
  rw [hP', hQ']

theorem QRAux.one_val_congr {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by subst h; rfl

end BaseEq

open _root_.CerednikDrinfeld.QM.FakeEllipticCurve _root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback.CerednikDrinfeld.QM.FakeEllipticCurve in
set_option maxHeartbeats 6400000 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (ℓ : ℕ)
    (u : WithExtraLevel Λ N ℓ S) (𝒟 : FakeEllipticCurve Λ N S) (hud : IsLevelIsogeny ℓ u 𝒟)
    (Ā Dbar : FakeEllipticCurve Λ N S')

    (g : Ā.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g Ā.f u.1.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Ā.f),
      (Ā.L.mul t' P Q).1 ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, Ā.act x ≫ g = g ≫ u.1.act x)
    (hg_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      FactorsThrough Ā.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g)
    (hg_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      (∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) → FactorsThrough Ā.lev P)

    (h : Dbar.A ⟶ 𝒟.A) (hh : CategoryTheory.IsPullback h Dbar.f 𝒟.f (Spec.map (CommRingCat.ofHom φ)))
    (hh_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Dbar.f),
      (Dbar.L.mul t' P Q).1 ≫ h =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1)
    (hh_act : ∀ x : ↥Λ, Dbar.act x ≫ h = h ≫ 𝒟.act x)
    (hh_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Dbar.f),
      FactorsThrough Dbar.lev P → ∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ h)
    (hh_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Dbar.f),
      (∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ h) → FactorsThrough Dbar.lev P) :
    ∃ Kbar : Ā.ExtraLevel ℓ,

      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
          FactorsThrough Kbar.levK P ↔ ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g) ∧
      IsLevelIsogeny ℓ (⟨Ā, Kbar⟩ : WithExtraLevel Λ N ℓ S') Dbar := by
  classical
  obtain ⟨φ₀, hφ₀, ψ₀, hψ₀, hmulφ, hmulψ, hactφ, hactψ, hcomp, hkerφ, hlevφ⟩ := hud

  have bcg_mul := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Ā.f) =>
    bc_mul g hg Ā.L u.1.L hg_mul t' P Q
  have bcg_one := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) => bc_one g hg Ā.L u.1.L hg_mul t'
  have bcg_inv := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f) =>
    bc_inv g hg Ā.L u.1.L hg_mul t' P
  have bcg_nsmul := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (P : SchemeHomOver t' Ā.f) =>
    bc_nsmul g hg Ā.L u.1.L hg_mul t' n P
  have bch_mul := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Dbar.f) =>
    bc_mul h hh Dbar.L 𝒟.L hh_mul t' P Q
  have bch_one := fun {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) => bc_one h hh Dbar.L 𝒟.L hh_mul t'

  have bcg_push : ∀ (x : ↥Λ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      bc g hg (pushPt (Ā.act x) (Ā.act_over x) P) = pushPt (u.1.act x) (u.1.act_over x) (bc g hg P) := by
    intro x T t' P
    apply Subtype.ext
    show (P.1 ≫ Ā.act x) ≫ g = (P.1 ≫ g) ≫ u.1.act x
    rw [Category.assoc, hg_act, Category.assoc]

  have hFTK : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      FactorsThrough (levKbar u Ā g) P ↔ FactorsThrough u.2.levK (bc g hg P) :=
    fun t' P => factorsThrough_levKbar_iff u Ā g P
  have hFTlev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      FactorsThrough Ā.lev P ↔ FactorsThrough u.1.lev (bc g hg P) :=
    fun t' P => ⟨hg_lev t' P, hg_lev' t' P⟩

  have hsub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t Ā.f),
      FactorsThrough (levKbar u Ā g) P → FactorsThrough (levKbar u Ā g) Q →
        FactorsThrough (levKbar u Ā g) (Ā.L.mul t P Q) ∧ FactorsThrough (levKbar u Ā g) (Ā.L.inv t P) := by
    intro T t P Q hP hQ
    rw [hFTK] at hP hQ
    have h12 := u.2.levK_sub _ (bc g hg P) (bc g hg Q) hP hQ
    refine ⟨(hFTK t _).2 ?_, (hFTK t _).2 ?_⟩
    · rw [bcg_mul]; exact h12.1
    · rw [bcg_inv]; exact h12.2
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')), FactorsThrough (levKbar u Ā g) (Ā.L.one t) := by
    intro T t
    rw [hFTK, bcg_one]
    exact u.2.levK_one _
  have htors : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t Ā.f),
      FactorsThrough (levKbar u Ā g) P → nsmulPt Ā.L t ℓ P = Ā.L.one t := by
    intro T t P hP
    rw [hFTK] at hP
    apply bc_injective g hg
    rw [bcg_nsmul, bcg_one]
    exact u.2.levK_torsion _ (bc g hg P) hP
  have hstable : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t Ā.f),
      FactorsThrough (levKbar u Ā g) P → FactorsThrough (levKbar u Ā g) (pushPt (Ā.act x) (Ā.act_over x) P) := by
    intro x T t P hP
    rw [hFTK] at hP ⊢
    rw [bcg_push]
    exact u.2.levK_stable x _ (bc g hg P) hP
  have hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t Ā.f),
      FactorsThrough (levKbar u Ā g) P → FactorsThrough Ā.lev P → P = Ā.L.one t := by
    intro T t P hP hL
    rw [hFTK] at hP
    rw [hFTlev] at hL
    apply bc_injective g hg
    rw [bcg_one]
    exact u.2.levK_disjoint _ (bc g hg P) hP hL

  have hgeom : ∀ (k : Type u) [Field k] (sk : S' →+* k),
      geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk.comp φ) := by
    intro k _ sk
    show Spec.map (CommRingCat.ofHom sk) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (sk.comp φ))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S' →+* k), (ℓ : k) ≠ 0 →
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) Ā.f // FactorsThrough (levKbar u Ā g) P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) Ā.f) =
          Ā.L.mul (geomPoint k sk) (e x) (e y) := by
    intro k _ _ sk hℓ
    obtain ⟨e₀, he₀⟩ := u.2.levK_fibre k (sk.comp φ) hℓ

    let fwd : {P : SchemeHomOver (geomPoint k sk) Ā.f // FactorsThrough (levKbar u Ā g) P} →
        {P : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f // FactorsThrough u.2.levK P} := fun P =>
      ⟨⟨P.1.1 ≫ g, by rw [← hgeom]; exact (bc g hg P.1).2⟩,
        factorsThrough_of_val_eq u.2.levK (bc g hg P.1) _ rfl ((hFTK _ P.1).1 P.2)⟩

    have hbwd_w : ∀ Q : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f,
        Q.1 ≫ u.1.f = geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) := by
      intro Q; rw [Q.2, hgeom]
    let bwd : {P : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f // FactorsThrough u.2.levK P} →
        {P : SchemeHomOver (geomPoint k sk) Ā.f // FactorsThrough (levKbar u Ā g) P} := fun Q =>
      ⟨⟨hg.lift Q.1.1 (geomPoint k sk) (hbwd_w Q.1), hg.lift_snd _ _ _⟩,
        (hFTK _ _).2 (factorsThrough_of_val_eq u.2.levK Q.1 _ (by
          show Q.1.1 = hg.lift Q.1.1 (geomPoint k sk) (hbwd_w Q.1) ≫ g
          rw [hg.lift_fst]) Q.2)⟩
    have hfb : ∀ P, bwd (fwd P) = P := by
      intro P
      apply Subtype.ext; apply Subtype.ext
      apply hg.hom_ext
      · rw [hg.lift_fst]
      · rw [hg.lift_snd]; exact P.1.2.symm
    have hbf : ∀ Q, fwd (bwd Q) = Q := by
      intro Q
      apply Subtype.ext; apply Subtype.ext
      show hg.lift Q.1.1 (geomPoint k sk) (hbwd_w Q.1) ≫ g = Q.1.1
      rw [hg.lift_fst]
    let β : {P : SchemeHomOver (geomPoint k sk) Ā.f // FactorsThrough (levKbar u Ā g) P} ≃
        {P : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f // FactorsThrough u.2.levK P} :=
      ⟨fwd, bwd, hfb, hbf⟩
    refine ⟨e₀.trans β.symm, fun x y => ?_⟩

    have hinj : ∀ P Q : SchemeHomOver (geomPoint k sk) Ā.f, P.1 ≫ g = Q.1 ≫ g → P = Q := by
      intro P Q hPQ
      apply Subtype.ext
      apply hg.hom_ext hPQ
      rw [P.2, Q.2]
    apply hinj
    have h1 : (((e₀.trans β.symm) (x + y) : {P : SchemeHomOver (geomPoint k sk) Ā.f // FactorsThrough (levKbar u Ā g) P}) :
        SchemeHomOver (geomPoint k sk) Ā.f).1 ≫ g = ((e₀ (x + y) : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f)).1 := by
      show (((bwd (e₀ (x + y))) : SchemeHomOver (geomPoint k sk) Ā.f)).1 ≫ g = _
      exact congrArg (fun Q : {P : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f // FactorsThrough u.2.levK P} =>
        ((Q : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f)).1) (hbf (e₀ (x + y)))
    have hx : ((((e₀.trans β.symm) x : {P : SchemeHomOver (geomPoint k sk) Ā.f // FactorsThrough (levKbar u Ā g) P}) :
        SchemeHomOver (geomPoint k sk) Ā.f)).1 ≫ g = ((e₀ x : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f)).1 := by
      show (((bwd (e₀ x)) : SchemeHomOver (geomPoint k sk) Ā.f)).1 ≫ g = _
      exact congrArg (fun Q : {P : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f // FactorsThrough u.2.levK P} =>
        ((Q : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f)).1) (hbf (e₀ x))
    have hy : ((((e₀.trans β.symm) y : {P : SchemeHomOver (geomPoint k sk) Ā.f // FactorsThrough (levKbar u Ā g) P}) :
        SchemeHomOver (geomPoint k sk) Ā.f)).1 ≫ g = ((e₀ y : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f)).1 := by
      show (((bwd (e₀ y)) : SchemeHomOver (geomPoint k sk) Ā.f)).1 ≫ g = _
      exact congrArg (fun Q : {P : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f // FactorsThrough u.2.levK P} =>
        ((Q : SchemeHomOver (geomPoint k (sk.comp φ)) u.1.f)).1) (hbf (e₀ y))
    rw [h1, he₀, hg_mul]

    exact QRAux.mul_val_congr u.1.L (hgeom k sk).symm _ _ _ _ hx.symm hy.symm
  let Kb : Ā.ExtraLevel ℓ :=
    { K := Kbar u Ā g, levK := levKbar u Ā g, levK_closed := levKbar_closed u Ā g,
      levK_sub := hsub, levK_one := hone, levK_torsion := htors, levK_stable := hstable, levK_disjoint := hdisj,
      levK_finite := levKbar_finite u Ā g hg, levK_flat := levKbar_flat u Ā g hg,
      levK_finitePresentation := levKbar_finitePresentation u Ā g hg, levK_rank := levKbar_rank u Ā g hg,
      levK_fibre := hfibre }
  refine ⟨Kb, fun t' P => factorsThrough_levKbar_iff u Ā g P, ?_⟩

  have hwφ : (g ≫ φ₀) ≫ 𝒟.f = Ā.f ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hφ₀]; exact hg.w
  have hwψ : (h ≫ ψ₀) ≫ u.1.f = Dbar.f ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, hψ₀]; exact hh.w
  let φb : Ā.A ⟶ Dbar.A := hh.lift (g ≫ φ₀) Ā.f hwφ
  let ψb : Dbar.A ⟶ Ā.A := hg.lift (h ≫ ψ₀) Dbar.f hwψ
  have hφb_h : φb ≫ h = g ≫ φ₀ := hh.lift_fst _ _ _
  have hφb : φb ≫ Dbar.f = Ā.f := hh.lift_snd _ _ _
  have hψb_g : ψb ≫ g = h ≫ ψ₀ := hg.lift_fst _ _ _
  have hψb : ψb ≫ Ā.f = Dbar.f := hg.lift_snd _ _ _

  have bc_mapφ : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      bc h hh (mapPt φb hφb P) = mapPt φ₀ hφ₀ (bc g hg P) := by
    intro T t' P; apply Subtype.ext
    show (P.1 ≫ φb) ≫ h = (P.1 ≫ g) ≫ φ₀
    rw [Category.assoc, hφb_h, Category.assoc]
  have bc_mapψ : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Dbar.f),
      bc g hg (mapPt ψb hψb P) = mapPt ψ₀ hψ₀ (bc h hh P) := by
    intro T t' P; apply Subtype.ext
    show (P.1 ≫ ψb) ≫ g = (P.1 ≫ h) ≫ ψ₀
    rw [Category.assoc, hψb_g, Category.assoc]
  have hφb_h' : ∀ {Z : Scheme.{u}} (k : 𝒟.A ⟶ Z), φb ≫ h ≫ k = g ≫ φ₀ ≫ k := fun k => by
    rw [← Category.assoc, hφb_h, Category.assoc]
  have hψb_g' : ∀ {Z : Scheme.{u}} (k : u.1.A ⟶ Z), ψb ≫ g ≫ k = h ≫ ψ₀ ≫ k := fun k => by
    rw [← Category.assoc, hψb_g, Category.assoc]
  refine ⟨φb, hφb, ψb, hψb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    apply bc_injective h hh
    rw [bc_mapφ, bcg_mul, hmulφ, bch_mul, bc_mapφ, bc_mapφ]
  ·
    intro T t P Q
    apply bc_injective g hg
    rw [bc_mapψ, bch_mul, hmulψ, bcg_mul, bc_mapψ, bc_mapψ]
  ·
    intro x
    apply hh.hom_ext
    · show (Ā.act x ≫ φb) ≫ h = (φb ≫ Dbar.act x) ≫ h
      rw [Category.assoc, hφb_h, ← Category.assoc, hg_act, Category.assoc, hactφ, Category.assoc, hh_act, hφb_h']
    · show (Ā.act x ≫ φb) ≫ Dbar.f = (φb ≫ Dbar.act x) ≫ Dbar.f
      rw [Category.assoc, hφb, Ā.act_over, Category.assoc, Dbar.act_over, hφb]
  ·
    intro x
    apply hg.hom_ext
    · show (Dbar.act x ≫ ψb) ≫ g = (ψb ≫ Ā.act x) ≫ g
      rw [Category.assoc, hψb_g, ← Category.assoc, hh_act, Category.assoc, hactψ, Category.assoc, hg_act, hψb_g']
    · show (Dbar.act x ≫ ψb) ≫ Ā.f = (ψb ≫ Ā.act x) ≫ Ā.f
      rw [Category.assoc, hψb, Dbar.act_over, Category.assoc, Ā.act_over, hψb]
  ·
    intro hℓ
    obtain ⟨h1, h2⟩ := hcomp hℓ
    constructor
    · apply hg.hom_ext
      · rw [Category.assoc, hψb_g, ← Category.assoc, hφb_h, Category.assoc, h1, hg_act]
      · rw [Category.assoc, hψb, hφb, Ā.act_over]
    · apply hh.hom_ext
      · rw [Category.assoc, hφb_h, ← Category.assoc, hψb_g, Category.assoc, h2, hh_act]
      · rw [Category.assoc, hφb, hψb, Dbar.act_over]
  ·
    intro T t P
    constructor
    · intro hP
      apply (hFTK t P).2
      apply (hkerφ _ (bc g hg P)).1
      rw [← bc_mapφ, hP, bch_one]
    · intro hP
      apply bc_injective h hh
      rw [bc_mapφ, bch_one]
      exact (hkerφ _ (bc g hg P)).2 ((hFTK t P).1 hP)
  ·
    intro T t P hP
    apply hh_lev' t
    have h1 := hlevφ _ (bc g hg P) ((hFTlev t P).1 hP)
    obtain ⟨P₀, hP₀⟩ := h1
    refine ⟨P₀, ?_⟩
    rw [hP₀]
    show ((bc g hg P).1 ≫ φ₀) = (P.1 ≫ φb) ≫ h
    rw [Category.assoc, hφb_h, ← Category.assoc]
    rfl

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback (solution)
