-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.isPullback_refl_comp_cancel_iso_unique_nsmulPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d5861601-bcb8-5054-9499-91dc44346530

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_refl_comp_cancel_iso_unique_nsmulPt

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace WflCalc

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : SchemeHomOver s' f :=
  ⟨P.1, P.2.trans h⟩

@[scoped simp] theorem castPt_coe {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : (castPt h P).1 = P.1 := rfl

theorem castPt_injective {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') {P Q : SchemeHomOver s f} (hPQ : castPt h P = castPt h Q) :
    P = Q :=
  Subtype.ext (by simpa [castPt] using congrArg Subtype.val hPQ)

theorem one_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') :
    L.one s' = castPt h (L.one s) := by
  subst h; rfl

theorem nsmulPt_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (n : ℕ) (P : SchemeHomOver s f) :
    nsmulPt L s' n (castPt h P) = castPt h (nsmulPt L s n P) := by
  subst h; rfl

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f)
    (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  cases Subtype.ext hP
  cases Subtype.ext hQ
  rfl

theorem nsmulPt_natural {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n x) x) =
      L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x)
    rw [L.mul_natural t t' ψ hψ, ih]

theorem nsmulPt_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂) (n : ℕ)
    (P₁ : SchemeHomOver t₁ f) (P₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) :
    (nsmulPt L t₁ n P₁).1 = (nsmulPt L t₂ n P₂).1 := by
  subst ht
  cases Subtype.ext hP
  rfl

theorem mapPt_nsmulPt {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A')
    (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero =>

    letI := L'.pointGroup t
    have h := hmul t (L.one t) (L.one t)
    rw [L.one_mul] at h
    have : mapPt φ hφ (L.one t) * mapPt φ hφ (L.one t) = mapPt φ hφ (L.one t) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hmul, ih]

section Square

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
  (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))

def gPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f) :
    (gPt hg P).1 = P.1 ≫ g := rfl

theorem gPt_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' E'.f}
    (h : gPt hg P = gPt hg Q) : P = Q := by
  apply Subtype.ext
  exact hg.hom_ext (congrArg Subtype.val h) (P.2.trans Q.2.symm)

def liftPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f) :
    SchemeHomOver t' E'.f :=
  ⟨hg.lift Q.1 t' Q.2, hg.lift_snd _ _ _⟩

theorem gPt_liftPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f) : gPt hg (liftPt hg Q) = Q := by
  apply Subtype.ext
  simp [gPt, liftPt]

variable
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
    (E'.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hmul

theorem gPt_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f) :
    gPt hg (E'.L.mul t' P Q) = E.L.mul _ (gPt hg P) (gPt hg Q) :=
  Subtype.ext (hmul t' P Q)

theorem gPt_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    gPt hg (E'.L.one t') = E.L.one _ := by
  letI := E.L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h := gPt_mul hg hmul t' (E'.L.one t') (E'.L.one t')
  rw [E'.L.one_mul] at h
  have : gPt hg (E'.L.one t') * gPt hg (E'.L.one t') = gPt hg (E'.L.one t') * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel this

theorem gPt_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (P : SchemeHomOver t' E'.f) :
    gPt hg (nsmulPt E'.L t' n P) = nsmulPt E.L _ n (gPt hg P) := by
  induction n with
  | zero => exact gPt_one hg hmul t'
  | succ n ih =>
    show gPt hg (E'.L.mul t' (nsmulPt E'.L t' n P) P) = E.L.mul _ (nsmulPt E.L _ n (gPt hg P)) (gPt hg P)
    rw [gPt_mul hg hmul, ih]

omit hmul in
theorem gPt_pushPt (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (x : ↥Λ) (P : SchemeHomOver t' E'.f) :
    gPt hg (pushPt (E'.act x) (E'.act_over x) P) = pushPt (E.act x) (E.act_over x) (gPt hg P) := by
  apply Subtype.ext
  simp only [gPt_coe, mapPt_coe, Category.assoc, hact x]

theorem comp_nsmulPt_of_comp_eq (X : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (Y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f) (h : Y.1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ X.1) (k : ℕ) :
    (nsmulPt E'.L (𝟙 (Spec (CommRingCat.of S'))) k Y).1 ≫ g =
      Spec.map (CommRingCat.ofHom φ) ≫ (nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) k X).1 := by
  have hid : Spec.map (CommRingCat.ofHom φ) ≫ 𝟙 (Spec (CommRingCat.of S)) = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ) := by
    simp
  have hY : gPt hg Y = castPt hid (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) rfl X) :=
    Subtype.ext h
  have h1 := congrArg Subtype.val (gPt_nsmul hg hmul (𝟙 _) k Y)
  rw [hY, nsmulPt_castPt, ← nsmulPt_natural] at h1
  simpa using h1

end Square

section PullbackLevel

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
  (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
    (E'.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
  (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)

def bcSection (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f :=
  ⟨hg.lift (Spec.map (CommRingCat.ofHom φ) ≫ P.1) (𝟙 _)
      (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]),
    hg.lift_snd _ _ _⟩

theorem bcSection_comp (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) :
    (bcSection hg P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ P.1 :=
  hg.lift_fst _ _ _

theorem eq_bcSection (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f) (h : P'.1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ P.1) :
    P' = bcSection hg P := by
  apply Subtype.ext
  apply hg.hom_ext
  · rw [h, bcSection_comp]
  · rw [P'.2, (bcSection hg P).2]

theorem geomPoint_comp (φ : S →+* S') (k : Type u) [Field k] (sk : S' →+* k) :
    geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk.comp φ) := by
  simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f} {P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f}
  (hPP' : P'.1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ P.1)

include hact hPP' in
theorem castPt_gPt_pushPt_sectionAt (k : Type u) [Field k] (sk : S' →+* k) (x : ↥Λ) :
    castPt (geomPoint_comp φ k sk) (gPt hg (pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k sk))) =
      pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k (sk.comp φ)) := by
  apply Subtype.ext
  simp only [castPt_coe, gPt_coe, mapPt_coe, FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc,
    hact x]
  rw [reassoc_of% hPP', ← geomPoint_comp φ k sk, Category.assoc]

include hmul in
theorem castPt_gPt_one (k : Type u) [Field k] (sk : S' →+* k) :
    castPt (geomPoint_comp φ k sk) (gPt hg (E'.L.one (geomPoint k sk))) = E.L.one (geomPoint k (sk.comp φ)) := by
  rw [gPt_one hg hmul, ← one_castPt]

theorem castPt_gPt_injective (k : Type u) [Field k] (sk : S' →+* k) (P₁ P₂ : SchemeHomOver (geomPoint k sk) E'.f)
    (h : castPt (geomPoint_comp φ k sk) (gPt hg P₁) = castPt (geomPoint_comp φ k sk) (gPt hg P₂)) : P₁ = P₂ :=
  gPt_injective hg (castPt_injective _ h)

include hmul hact in

def pullbackLevel {m : ℕ} (P : E.FullLevel m) : E'.FullLevel m where
  P := bcSection hg P.P
  torsion := by
    apply gPt_injective hg
    apply Subtype.ext
    rw [gPt_coe, gPt_coe, comp_nsmulPt_of_comp_eq hg hmul P.P (bcSection hg P.P) (bcSection_comp hg P.P) m, P.torsion]
    have h2 := congrArg Subtype.val (gPt_one hg hmul (𝟙 (Spec (CommRingCat.of S'))))
    rw [gPt_coe] at h2
    rw [h2]
    exact congrArg Subtype.val (E.L.one_natural (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom φ)) (by simp))
  generates := by
    intro k _ _ sk T' hT'
    have hb := geomPoint_comp φ k sk
    set T := castPt hb (gPt hg T') with hT
    have hTtors : nsmulPt E.L (geomPoint k (sk.comp φ)) m T = E.L.one (geomPoint k (sk.comp φ)) := by
      rw [hT, nsmulPt_castPt, ← gPt_nsmul hg hmul, hT', castPt_gPt_one hg hmul]
    obtain ⟨x, hx⟩ := P.generates k (sk.comp φ) T hTtors
    refine ⟨x, ?_⟩
    apply castPt_gPt_injective hg k sk
    rw [castPt_gPt_pushPt_sectionAt hg hact (bcSection_comp hg P.P) k sk x, hx]
  annihilator := by
    intro k _ _ sk x
    rw [← P.annihilator k (sk.comp φ) x, ← castPt_gPt_pushPt_sectionAt hg hact (bcSection_comp hg P.P) k sk x,
      ← castPt_gPt_one hg hmul k sk]
    exact ⟨fun h => by rw [h], fun h => castPt_gPt_injective hg k sk _ _ h⟩

theorem pullbackLevel_P {m : ℕ} (P : E.FullLevel m) :
    (pullbackLevel hg hmul hact P).P = bcSection hg P.P := rfl

end PullbackLevel

theorem specMap_id (S : Type u) [CommRing S] :
    Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem specMap_comp {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem isPullback_refl {k : ℕ} (S : Type u) [CommRing S] (u : FakeEllipticCurve.WithFullLevel Λ N k S) :
    FakeEllipticCurve.WithFullLevel.IsPullback (RingHom.id S) u u := by
  have hsq : IsPullback (𝟙 u.1.A) u.1.f u.1.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [specMap_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨𝟙 _, hsq, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [Category.comp_id]
    apply mul_val_congr u.1.L
    · rw [specMap_id, Category.comp_id]
    · simp
    · simp
  · intro x; simp
  · intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hP
    exact ⟨P₀, by rw [hP₀, Category.comp_id]⟩
  · rw [specMap_id, Category.comp_id, Category.id_comp]

theorem isPullback_comp {k : ℕ} {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S')
    (ψ : S' →+* S'') (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
    (u'' : FakeEllipticCurve.WithFullLevel Λ N k S'')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (h' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'') :
    FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'' := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := h
  obtain ⟨g', hg', hmul', hact', hlev', hP'⟩ := h'
  have hsq : IsPullback (g' ≫ g) u''.1.f u.1.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [specMap_comp]
    exact hg'.paste_horiz hg
  refine ⟨g' ≫ g, hsq, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [← Category.assoc, hmul' t P Q, hmul]
    apply mul_val_congr u.1.L
    · rw [specMap_comp, Category.assoc]
    · simp
    · simp
  · intro x
    rw [← Category.assoc, hact' x, Category.assoc, hact x, Category.assoc]
  · intro T t P hPl
    obtain ⟨P₁, hP₁⟩ := hlev' t P hPl
    obtain ⟨P₀, hP₀⟩ := hlev (t ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
      ⟨P₁, hP₁⟩
    exact ⟨P₀, by rw [hP₀, Category.assoc]⟩
  · rw [← Category.assoc, hP', Category.assoc, hP, ← Category.assoc, ← specMap_comp]

theorem isPullback_cancel {k : ℕ} {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S')
    (ψ : S' →+* S'') (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
    (u'' : FakeEllipticCurve.WithFullLevel Λ N k S'')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
    (h'' : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'') :
    FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'' := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := h
  obtain ⟨g₂, hg₂, hmul₂, hact₂, hlev₂, hP₂⟩ := h''

  have hcond : g₂ ≫ u.1.f = (u''.1.f ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [hg₂.w, specMap_comp, Category.assoc]
  let G : u''.1.A ⟶ u'.1.A := hg.lift g₂ (u''.1.f ≫ Spec.map (CommRingCat.ofHom ψ)) hcond
  have hGg : G ≫ g = g₂ := hg.lift_fst _ _ _
  have hGf : G ≫ u'.1.f = u''.1.f ≫ Spec.map (CommRingCat.ofHom ψ) := hg.lift_snd _ _ _
  have hGpb : IsPullback G u''.1.f u'.1.f (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ hGf hg
    rw [hGg, ← specMap_comp]
    exact hg₂

  have hGmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'')) (P₀ Q₀ : SchemeHomOver t' u''.1.f),
      (u''.1.L.mul t' P₀ Q₀).1 ≫ G =
        (u'.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ψ))
          ⟨P₀.1 ≫ G, by rw [Category.assoc, hGpb.w, ← Category.assoc, P₀.2]⟩
          ⟨Q₀.1 ≫ G, by rw [Category.assoc, hGpb.w, ← Category.assoc, Q₀.2]⟩).1 := by
    intro T t' P₀ Q₀
    apply hg.hom_ext
    · rw [Category.assoc, hGg, hmul₂ t' P₀ Q₀, hmul]
      apply mul_val_congr u.1.L
      · rw [Category.assoc, specMap_comp]
      · simp only [Category.assoc, hGg]
      · simp only [Category.assoc, hGg]
    · rw [(u'.1.L.mul _ _ _).2, Category.assoc ((u''.1.L.mul t' P₀ Q₀).1) G u'.1.f, hGf, ← Category.assoc,
        (u''.1.L.mul t' P₀ Q₀).2]

  have hGact : ∀ x : ↥Λ, u''.1.act x ≫ G = G ≫ u'.1.act x := by
    intro x
    apply hg.hom_ext
    · rw [Category.assoc, hGg, hact₂, Category.assoc, hact, ← Category.assoc, hGg]
    · rw [Category.assoc, hGf, ← Category.assoc, u''.1.act_over, Category.assoc, u'.1.act_over, hGf]
  refine ⟨G, hGpb, hGmul, hGact, ?_, ?_⟩
  ·
    intro T t' Pt hPt
    obtain ⟨P₀, hP₀⟩ := hlev₂ t' Pt hPt
    exact FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback φ u.1 u'.1 g hg hmul hlev
      (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨Pt.1 ≫ G, by rw [Category.assoc, hGpb.w, ← Category.assoc, Pt.2]⟩
      ⟨P₀, by rw [hP₀, Category.assoc, hGg]⟩
  ·
    apply hg.hom_ext
    · rw [Category.assoc, hGg, hP₂, Category.assoc, hP, ← Category.assoc, ← specMap_comp]
    · rw [Category.assoc, hGf, ← Category.assoc, (u''.2.P).2, Category.assoc, (u'.2.P).2, Category.id_comp,
        Category.comp_id]

theorem mapPt_hom_mapPt_inv {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f') :
    mapPt e.hom he (mapPt e.inv he' P) = P :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id])

theorem mapPt_inv_mapPt_hom {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (he' : e.inv ≫ f = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt e.inv he' (mapPt e.hom he P) = P :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id])

theorem isPullback_of_isPullback_of_iso {k : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u'' u' : FakeEllipticCurve.WithFullLevel Λ N k S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u'') (hiso : FakeEllipticCurve.WithFullLevel.Iso u'' u') :
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := h
  obtain ⟨e, he, emul, eact, elev, eP⟩ := hiso
  have he' : e.inv ≫ u''.1.f = u'.1.f := by rw [← he, Iso.inv_hom_id_assoc]
  have sq : IsPullback e.inv u'.1.f u''.1.f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩
  have HG : IsPullback (e.inv ≫ g) u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)) := by
    have := sq.paste_horiz hg
    rwa [Category.id_comp] at this
  refine ⟨e.inv ≫ g, HG, ?_, ?_, ?_, ?_⟩
  · intro T t' P Q
    set P₁ : SchemeHomOver t' u''.1.f := mapPt e.inv he' P with hP₁
    set Q₁ : SchemeHomOver t' u''.1.f := mapPt e.inv he' Q with hQ₁
    have hPQ : u'.1.L.mul t' P Q = mapPt e.hom he (u''.1.L.mul t' P₁ Q₁) := by
      rw [emul t' P₁ Q₁, hP₁, hQ₁, mapPt_hom_mapPt_inv, mapPt_hom_mapPt_inv]
    have h1 : (u'.1.L.mul t' P Q).1 ≫ e.inv ≫ g = (u''.1.L.mul t' P₁ Q₁).1 ≫ g := by
      rw [hPQ, mapPt_coe, Category.assoc, Iso.hom_inv_id_assoc]
    rw [h1, hmul t' P₁ Q₁]
    congr 2
  · intro x
    have h1 : u'.1.act x ≫ e.inv = e.inv ≫ u''.1.act x := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← eact x, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, h1, Category.assoc, hact x, Category.assoc]
  · intro T t' P hPl
    have h1 : FactorsThrough u''.1.lev (mapPt e.inv he' P) := by
      rw [elev t' (mapPt e.inv he' P), mapPt_hom_mapPt_inv]
      exact hPl
    obtain ⟨P₀, hP₀⟩ := hlev t' (mapPt e.inv he' P) h1
    exact ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc]⟩
  · have h1 : (u'.2.P).1 = (u''.2.P).1 ≫ e.hom := by rw [← eP, mapPt_coe]
    rw [h1, Category.assoc, Iso.hom_inv_id_assoc, hP]

theorem isPullback_of_iso_of_isPullback {k : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u₁ u₂ : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
    (hiso : FakeEllipticCurve.WithFullLevel.Iso u₁ u₂) (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u₁ u') :
    FakeEllipticCurve.WithFullLevel.IsPullback φ u₂ u' := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := h
  obtain ⟨e, he, emul, eact, elev, eP⟩ := hiso
  have sq : IsPullback e.hom u₁.1.f u₂.1.f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have HG : IsPullback (g ≫ e.hom) u'.1.f u₂.1.f (Spec.map (CommRingCat.ofHom φ)) := by
    have := hg.paste_horiz sq
    rwa [Category.comp_id] at this
  refine ⟨g ≫ e.hom, HG, ?_, ?_, ?_, ?_⟩
  · intro T t' P Q
    have h1 := hmul t' P Q
    have h2 := congrArg Subtype.val (emul (t' ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at h2
    rw [← Category.assoc, h1, h2]
    apply mul_val_congr u₂.1.L rfl
    · simp
    · simp
  · intro x
    rw [← Category.assoc, hact x, Category.assoc, eact x, Category.assoc]
  · intro T t' P hPl
    obtain ⟨P₀, hP₀⟩ := hlev t' P hPl
    have h1 : FactorsThrough u₁.1.lev
        (⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) u₁.1.f) := ⟨P₀, hP₀⟩
    rw [elev] at h1
    obtain ⟨P₁, hP₁⟩ := h1
    exact ⟨P₁, by rw [hP₁, mapPt_coe, Category.assoc]⟩
  · rw [← Category.assoc, hP, Category.assoc, ← mapPt_coe e.hom he u₁.2.P, eP]

theorem iso_of_isPullback_of_isPullback {k : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' u'' : FakeEllipticCurve.WithFullLevel Λ N k S')
    (h' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (h'' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u'') :
    FakeEllipticCurve.WithFullLevel.Iso u' u'' := by
  obtain ⟨g₁, hg₁, hmul₁, hact₁, hlev₁, hP₁⟩ := h'
  obtain ⟨g₂, hg₂, hmul₂, hact₂, hlev₂, hP₂⟩ := h''
  let e : u'.1.A ≅ u''.1.A := hg₁.isoIsPullback _ _ hg₂
  have he_g : e.hom ≫ g₂ = g₁ := hg₁.isoIsPullback_hom_fst _ _ hg₂
  have he_f : e.hom ≫ u''.1.f = u'.1.f := hg₁.isoIsPullback_hom_snd _ _ hg₂
  refine ⟨e, he_f, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    apply Subtype.ext
    apply hg₂.hom_ext
    · rw [mapPt_coe, Category.assoc, he_g, hmul₁ t P Q, hmul₂]
      apply mul_val_congr u.1.L rfl
      · simp only [mapPt_coe, Category.assoc, he_g]
      · simp only [mapPt_coe, Category.assoc, he_g]
    · rw [mapPt_coe, Category.assoc, he_f, (u'.1.L.mul t P Q).2, (u''.1.L.mul t _ _).2]
  ·
    intro x
    apply hg₂.hom_ext
    · rw [Category.assoc, he_g, hact₁ x, Category.assoc, hact₂ x, ← Category.assoc, he_g]
    · rw [Category.assoc, he_f, u'.1.act_over, Category.assoc, u''.1.act_over, he_f]
  ·
    intro T t P
    constructor
    · intro hPl
      obtain ⟨P₀, hP₀⟩ := hlev₁ t P hPl
      exact FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback φ u.1 u''.1 g₂ hg₂ hmul₂ hlev₂ t
        (mapPt e.hom he_f P) ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc, he_g]⟩
    · intro hPl
      obtain ⟨P₀, hP₀⟩ := hlev₂ t (mapPt e.hom he_f P) hPl
      exact FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback φ u.1 u'.1 g₁ hg₁ hmul₁ hlev₁ t P
        ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc, he_g]⟩
  ·
    apply Subtype.ext
    apply hg₂.hom_ext
    · rw [mapPt_coe, Category.assoc, he_g, hP₁, hP₂]
    · rw [mapPt_coe, Category.assoc, he_f, (u'.2.P).2, (u''.2.P).2]

theorem exists_nsmulPt_isPullback {k : ℕ} (n k' : ℕ) {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
    (P : u.1.FullLevel k') (hP : P.P = nsmulPt u.1.L (𝟙 (Spec (CommRingCat.of S))) n u.2.P)
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') :
    ∃ P' : u'.1.FullLevel k', P'.P = nsmulPt u'.1.L (𝟙 (Spec (CommRingCat.of S'))) n u'.2.P ∧
      FakeEllipticCurve.WithFullLevel.IsPullback φ (⟨u.1, P⟩ : FakeEllipticCurve.WithFullLevel Λ N k' S) ⟨u'.1, P'⟩ := by
  obtain ⟨g, hg, hmul, hact, hlev, hgen⟩ := h
  refine ⟨pullbackLevel hg hmul hact P, ?_, g, hg, hmul, hact, hlev, ?_⟩
  ·
    rw [pullbackLevel_P]
    symm
    apply eq_bcSection hg
    rw [comp_nsmulPt_of_comp_eq hg hmul u.2.P u'.2.P hgen n, hP]
  · exact bcSection_comp hg P.P

theorem iso_nsmulPt {k : ℕ} (n k' : ℕ) {S : Type u} [CommRing S] (u₁ u₂ : FakeEllipticCurve.WithFullLevel Λ N k S)
    (Q₁ : u₁.1.FullLevel k') (Q₂ : u₂.1.FullLevel k')
    (hQ₁ : Q₁.P = nsmulPt u₁.1.L (𝟙 (Spec (CommRingCat.of S))) n u₁.2.P)
    (hQ₂ : Q₂.P = nsmulPt u₂.1.L (𝟙 (Spec (CommRingCat.of S))) n u₂.2.P)
    (hiso : FakeEllipticCurve.WithFullLevel.Iso u₁ u₂) :
    FakeEllipticCurve.WithFullLevel.Iso (⟨u₁.1, Q₁⟩ : FakeEllipticCurve.WithFullLevel Λ N k' S) ⟨u₂.1, Q₂⟩ := by
  obtain ⟨e, he, emul, eact, elev, eP⟩ := hiso
  refine ⟨e, he, emul, eact, elev, ?_⟩
  show mapPt e.hom he Q₁.P = Q₂.P
  rw [hQ₁, hQ₂, mapPt_nsmulPt u₁.1.L u₂.1.L e.hom he emul, eP]

end WflCalc
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_refl_comp_cancel_iso_unique_nsmulPt.WflCalc"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_refl_comp_cancel_iso_unique_nsmulPt.WflCalc"

open WflCalc in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N k : ℕ) :
    (∀ (S : Type u) [CommRing S] (u : FakeEllipticCurve.WithFullLevel Λ N k S),
        FakeEllipticCurve.WithFullLevel.IsPullback (RingHom.id S) u u) ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
        (u'' : FakeEllipticCurve.WithFullLevel Λ N k S''),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'' →
          FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'') ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
        (u'' : FakeEllipticCurve.WithFullLevel Λ N k S''),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'' →
          FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' u'' : FakeEllipticCurve.WithFullLevel Λ N k S'),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.Iso u' u'' →
          FakeEllipticCurve.WithFullLevel.IsPullback φ u u'') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u₁ u₂ : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S'),
        FakeEllipticCurve.WithFullLevel.Iso u₁ u₂ → FakeEllipticCurve.WithFullLevel.IsPullback φ u₁ u' →
          FakeEllipticCurve.WithFullLevel.IsPullback φ u₂ u') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' u'' : FakeEllipticCurve.WithFullLevel Λ N k S'),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.IsPullback φ u u'' →
          FakeEllipticCurve.WithFullLevel.Iso u' u'') ∧
    (∀ (n k' : ℕ) (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
        (P : u.1.FullLevel k'), P.P = nsmulPt u.1.L (𝟙 (Spec (CommRingCat.of S))) n u.2.P →
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' →
          ∃ P' : u'.1.FullLevel k', P'.P = nsmulPt u'.1.L (𝟙 (Spec (CommRingCat.of S'))) n u'.2.P ∧
            FakeEllipticCurve.WithFullLevel.IsPullback φ (⟨u.1, P⟩ : FakeEllipticCurve.WithFullLevel Λ N k' S)
              ⟨u'.1, P'⟩) ∧
    (∀ (n k' : ℕ) (S : Type u) [CommRing S] (u₁ u₂ : FakeEllipticCurve.WithFullLevel Λ N k S)
        (Q₁ : u₁.1.FullLevel k') (Q₂ : u₂.1.FullLevel k'),
        Q₁.P = nsmulPt u₁.1.L (𝟙 (Spec (CommRingCat.of S))) n u₁.2.P →
        Q₂.P = nsmulPt u₂.1.L (𝟙 (Spec (CommRingCat.of S))) n u₂.2.P →
        FakeEllipticCurve.WithFullLevel.Iso u₁ u₂ →
          FakeEllipticCurve.WithFullLevel.Iso (⟨u₁.1, Q₁⟩ : FakeEllipticCurve.WithFullLevel Λ N k' S) ⟨u₂.1, Q₂⟩) :=
  ⟨fun S _ u => isPullback_refl S u,
   fun _ _ _ _ _ _ φ ψ u u' u'' h h' => isPullback_comp φ ψ u u' u'' h h',
   fun _ _ _ _ _ _ φ ψ u u' u'' h h'' => isPullback_cancel φ ψ u u' u'' h h'',
   fun _ _ _ _ φ u u' u'' h hiso => isPullback_of_isPullback_of_iso φ u u' u'' h hiso,
   fun _ _ _ _ φ u₁ u₂ u' hiso h => isPullback_of_iso_of_isPullback φ u₁ u₂ u' hiso h,
   fun _ _ _ _ φ u u' u'' h' h'' => iso_of_isPullback_of_isPullback φ u u' u'' h' h'',
   fun n k' _ _ _ _ φ u u' P hP h => exists_nsmulPt_isPullback n k' φ u u' P hP h,
   fun n k' _ _ u₁ u₂ Q₁ Q₂ hQ₁ hQ₂ hiso => iso_nsmulPt n k' u₁ u₂ Q₁ Q₂ hQ₁ hQ₂ hiso⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_refl_comp_cancel_iso_unique_nsmulPt
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_refl_comp_cancel_iso_unique_nsmulPt (solution)
