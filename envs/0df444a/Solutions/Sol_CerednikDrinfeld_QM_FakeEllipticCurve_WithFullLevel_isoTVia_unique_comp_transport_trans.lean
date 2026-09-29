-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.isoTVia_unique_comp_transport_trans
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/164a9623-b4f7-563a-a144-d96c45dccb0e

import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_levK_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isoTVia_unique_comp_transport_trans

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace KitT

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f)
    (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  cases Subtype.ext hP
  cases Subtype.ext hQ
  rfl

theorem specMap_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem mapPt_mapPt {S : Type} [CommRing S] {A A' A'' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)} {f'' : A'' ⟶ Spec (CommRingCat.of S)}
    (e : A ⟶ A') (he : e ≫ f' = f) (e' : A' ⟶ A'') (he' : e' ≫ f'' = f')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt e' he' (mapPt e he P) = mapPt (e ≫ e') (by rw [Category.assoc, he', he]) P :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc])

theorem unique {S B : Type} [CommRing S] [CommRing B] (χ : S →+* B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (Cu : u.1.ExtraLevel ℓ)
    (v v' : FakeEllipticCurve.WithFullLevel Λ N m B) (Cv : v.1.ExtraLevel ℓ) (Cv' : v'.1.ExtraLevel ℓ)
    (g : v.1.A ⟶ u.1.A) (g' : v'.1.A ⟶ u.1.A)
    (h₁ : FakeEllipticCurve.IsPullbackVia χ u.1 v.1 g) (hP₁ : (v.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom χ) ≫ (u.2.P).1)
    (hC₁ : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' v.1.f),
      FactorsThrough Cv.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g)
    (h₂ : FakeEllipticCurve.IsPullbackVia χ u.1 v'.1 g') (hP₂ : (v'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom χ) ≫ (u.2.P).1)
    (hC₂ : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' v'.1.f),
      FactorsThrough Cv'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g') :
    ∃ (e : v.1.A ≅ v'.1.A) (he : e.hom ≫ v'.1.f = v.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia v v' Cv Cv' e he := by
  obtain ⟨hg₁, hmul₁, hact₁, hlev₁⟩ := h₁
  obtain ⟨hg₂, hmul₂, hact₂, hlev₂⟩ := h₂
  let e : v.1.A ≅ v'.1.A := hg₁.isoIsPullback _ _ hg₂
  have he_g : e.hom ≫ g' = g := hg₁.isoIsPullback_hom_fst _ _ hg₂
  have he_f : e.hom ≫ v'.1.f = v.1.f := hg₁.isoIsPullback_hom_snd _ _ hg₂
  refine ⟨e, he_f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro T t P Q
    apply Subtype.ext
    apply hg₂.hom_ext
    · rw [mapPt_coe, Category.assoc, he_g, hmul₁ t P Q, hmul₂]
      apply mul_val_congr u.1.L rfl
      · simp only [mapPt_coe, Category.assoc, he_g]
      · simp only [mapPt_coe, Category.assoc, he_g]
    · rw [mapPt_coe, Category.assoc, he_f, (v.1.L.mul t P Q).2, (v'.1.L.mul t _ _).2]
  · intro x
    apply hg₂.hom_ext
    · rw [Category.assoc, he_g, hact₁ x, Category.assoc, hact₂ x, ← Category.assoc, he_g]
    · rw [Category.assoc, he_f, v.1.act_over, Category.assoc, v'.1.act_over, he_f]
  · intro T t P
    constructor
    · intro hPl
      obtain ⟨P₀, hP₀⟩ := hlev₁ t P hPl
      exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback χ u.1 v'.1 g' hg₂ hmul₂ hlev₂ t
        (mapPt e.hom he_f P) ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc, he_g]⟩
    · intro hPl
      obtain ⟨P₀, hP₀⟩ := hlev₂ t (mapPt e.hom he_f P) hPl
      exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback χ u.1 v.1 g hg₁ hmul₁ hlev₁ t P
        ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc, he_g]⟩
  · apply Subtype.ext
    apply hg₂.hom_ext
    · rw [mapPt_coe, Category.assoc, he_g, hP₁, hP₂]
    · rw [mapPt_coe, Category.assoc, he_f, (v.2.P).2, (v'.2.P).2]
  · intro T t P
    constructor
    · intro hPl
      obtain ⟨P₀, hP₀⟩ := hC₁ t P hPl
      exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_levK_of_exists_comp_eq_of_isPullback χ ⟨u.1, Cu⟩ ⟨v'.1, Cv'⟩ g' hg₂
        hC₂ t (mapPt e.hom he_f P) ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc, he_g]⟩
    · intro hPl
      obtain ⟨P₀, hP₀⟩ := hC₂ t (mapPt e.hom he_f P) hPl
      exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_levK_of_exists_comp_eq_of_isPullback χ ⟨u.1, Cu⟩ ⟨v.1, Cv⟩ g hg₁
        hC₁ t P ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc, he_g]⟩

private theorem _root_.KitT.comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (u'' : FakeEllipticCurve.WithFullLevel Λ N m S'')
    (Cu : u.1.ExtraLevel ℓ) (Cu' : u'.1.ExtraLevel ℓ) (Cu'' : u''.1.ExtraLevel ℓ)
    (g : u'.1.A ⟶ u.1.A) (g' : u''.1.A ⟶ u'.1.A)
    (h : FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g) (hP : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1)
    (hC : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g)
    (h' : FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g') (hP' : (u''.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1)
    (hC' : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
      FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu'.K, P₀ ≫ Cu'.levK = P.1 ≫ g') :
    FakeEllipticCurve.IsPullbackVia (ψ.comp φ) u.1 u''.1 (g' ≫ g) ∧
      (u''.2.P).1 ≫ (g' ≫ g) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ (u.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
        FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ (g' ≫ g)) := by
  obtain ⟨hg, hmul, hact, hlev⟩ := h
  obtain ⟨hg', hmul', hact', hlev'⟩ := h'
  have hsq : IsPullback (g' ≫ g) u''.1.f u.1.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [specMap_comp]
    exact hg'.paste_horiz hg
  refine ⟨⟨hsq, ?_, ?_, ?_⟩, ?_, ?_⟩
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
  · intro T t P hPl
    obtain ⟨P₁, hP₁⟩ := hC' t P hPl
    obtain ⟨P₀, hP₀⟩ := hC (t ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
      ⟨P₁, hP₁⟩
    exact ⟨P₀, by rw [hP₀, Category.assoc]⟩

p2m_export "KitT" "comp"

theorem transport {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u w : FakeEllipticCurve.WithFullLevel Λ N m S) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (e : u.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = u.1.f)
    (hiso : FakeEllipticCurve.WithFullLevel.IsoTVia u w Cu Cw e he)
    (u' : FakeEllipticCurve.WithFullLevel Λ N m S') (Cu' : u'.1.ExtraLevel ℓ) (g : u'.1.A ⟶ u.1.A)
    (h : FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g) (hP : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1)
    (hC : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) :
    FakeEllipticCurve.IsPullbackVia φ w.1 u'.1 (g ≫ e.hom) ∧
      (u'.2.P).1 ≫ (g ≫ e.hom) = Spec.map (CommRingCat.ofHom φ) ≫ (w.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
        FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ (g ≫ e.hom)) := by
  obtain ⟨hg, hmul, hact, hlev⟩ := h
  obtain ⟨⟨emul, eact, elev, eP⟩, eC⟩ := hiso
  have sq : IsPullback e.hom u.1.f w.1.f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have HG : IsPullback (g ≫ e.hom) u'.1.f w.1.f (Spec.map (CommRingCat.ofHom φ)) := by
    have := hg.paste_horiz sq
    rwa [Category.comp_id] at this
  refine ⟨⟨HG, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro T t' P Q
    have h1 := hmul t' P Q
    have h2 := congrArg Subtype.val (emul (t' ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at h2
    rw [← Category.assoc, h1, h2]
    apply mul_val_congr w.1.L rfl
    · simp
    · simp
  · intro x
    rw [← Category.assoc, hact x, Category.assoc, eact x, Category.assoc]
  · intro T t' P hPl
    obtain ⟨P₀, hP₀⟩ := hlev t' P hPl
    have h1 : FactorsThrough u.1.lev
        (⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) u.1.f) := ⟨P₀, hP₀⟩
    rw [elev] at h1
    obtain ⟨P₁, hP₁⟩ := h1
    exact ⟨P₁, by rw [hP₁, mapPt_coe, Category.assoc]⟩
  · rw [← Category.assoc, hP, Category.assoc, ← mapPt_coe e.hom he u.2.P, eP]
  · intro T t' P hPl
    obtain ⟨P₀, hP₀⟩ := hC t' P hPl
    have h1 : FactorsThrough Cu.levK
        (⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) u.1.f) := ⟨P₀, hP₀⟩
    rw [eC] at h1
    obtain ⟨P₁, hP₁⟩ := h1
    exact ⟨P₁, by rw [hP₁, mapPt_coe, Category.assoc]⟩

theorem trans {S : Type} [CommRing S] (u v w : FakeEllipticCurve.WithFullLevel Λ N m S)
    (Cu : u.1.ExtraLevel ℓ) (Cv : v.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (h₁ : ∃ (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u v Cu Cv e he)
    (h₂ : ∃ (e : v.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = v.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia v w Cv Cw e he) :
    ∃ (e : u.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u w Cu Cw e he := by
  obtain ⟨e₁, he₁, ⟨m₁, a₁, l₁, p₁⟩, c₁⟩ := h₁
  obtain ⟨e₂, he₂, ⟨m₂, a₂, l₂, p₂⟩, c₂⟩ := h₂
  have he : (e₁ ≪≫ e₂).hom ≫ w.1.f = u.1.f := by rw [Iso.trans_hom, Category.assoc, he₂, he₁]
  have hmp : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t u.1.f),
      mapPt (e₁ ≪≫ e₂).hom he P = mapPt e₂.hom he₂ (mapPt e₁.hom he₁ P) := fun P =>
    Subtype.ext (by simp only [mapPt_coe, Iso.trans_hom, Category.assoc])
  refine ⟨e₁ ≪≫ e₂, he, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro T t P Q
    rw [hmp, hmp, hmp, m₁, m₂]
  · intro x
    rw [Iso.trans_hom, ← Category.assoc, a₁, Category.assoc, a₂, Category.assoc]
  · intro T t P
    rw [l₁, l₂, hmp]
  · rw [hmp, p₁, p₂]
  · intro T t P
    rw [c₁, c₂, hmp]

end KitT

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m ℓ : ℕ) :

    (∀ (S B : Type) [CommRing S] [CommRing B] (χ : S →+* B)
        (u : FakeEllipticCurve.WithFullLevel Λ N m S) (Cu : u.1.ExtraLevel ℓ)
        (v v' : FakeEllipticCurve.WithFullLevel Λ N m B) (Cv : v.1.ExtraLevel ℓ) (Cv' : v'.1.ExtraLevel ℓ)
        (g : v.1.A ⟶ u.1.A) (g' : v'.1.A ⟶ u.1.A),
        FakeEllipticCurve.IsPullbackVia χ u.1 v.1 g → (v.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom χ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' v.1.f),
          FactorsThrough Cv.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) →
        FakeEllipticCurve.IsPullbackVia χ u.1 v'.1 g' → (v'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom χ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' v'.1.f),
          FactorsThrough Cv'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g') →
        ∃ (e : v.1.A ≅ v'.1.A) (he : e.hom ≫ v'.1.f = v.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia v v' Cv Cv' e he) ∧

    (∀ (S S' S'' : Type) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
        (u'' : FakeEllipticCurve.WithFullLevel Λ N m S'')
        (Cu : u.1.ExtraLevel ℓ) (Cu' : u'.1.ExtraLevel ℓ) (Cu'' : u''.1.ExtraLevel ℓ)
        (g : u'.1.A ⟶ u.1.A) (g' : u''.1.A ⟶ u'.1.A),
        FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g → (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) →
        FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g' → (u''.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu'.K, P₀ ≫ Cu'.levK = P.1 ≫ g') →
        FakeEllipticCurve.IsPullbackVia (ψ.comp φ) u.1 u''.1 (g' ≫ g) ∧ (u''.2.P).1 ≫ (g' ≫ g) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ (u.2.P).1 ∧
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ (g' ≫ g))) ∧

    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u w : FakeEllipticCurve.WithFullLevel Λ N m S) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
        (e : u.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = u.1.f),
        FakeEllipticCurve.WithFullLevel.IsoTVia u w Cu Cw e he →
        ∀ (u' : FakeEllipticCurve.WithFullLevel Λ N m S') (Cu' : u'.1.ExtraLevel ℓ) (g : u'.1.A ⟶ u.1.A),
        FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g → (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) →
        FakeEllipticCurve.IsPullbackVia φ w.1 u'.1 (g ≫ e.hom) ∧ (u'.2.P).1 ≫ (g ≫ e.hom) = Spec.map (CommRingCat.ofHom φ) ≫ (w.2.P).1 ∧
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ (g ≫ e.hom))) ∧

    (∀ (S : Type) [CommRing S] (u v w : FakeEllipticCurve.WithFullLevel Λ N m S)
        (Cu : u.1.ExtraLevel ℓ) (Cv : v.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ),
        (∃ (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u v Cu Cv e he) → (∃ (e : v.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = v.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia v w Cv Cw e he) →
        ∃ (e : u.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u w Cu Cw e he) :=
  ⟨fun S B _ _ χ u Cu v v' Cv Cv' g g' h₁ hP₁ hC₁ h₂ hP₂ hC₂ => KitT.unique χ u Cu v v' Cv Cv' g g' h₁ hP₁ hC₁ h₂ hP₂ hC₂,
   fun S S' S'' _ _ _ φ ψ u u' u'' Cu Cu' Cu'' g g' h hP hC h' hP' hC' =>
     KitT.comp φ ψ u u' u'' Cu Cu' Cu'' g g' h hP hC h' hP' hC',
   fun S S' _ _ φ u w Cu Cw e he hiso u' Cu' g h hP hC => KitT.transport φ u w Cu Cw e he hiso u' Cu' g h hP hC,
   fun S _ u v w Cu Cv Cw h₁ h₂ => KitT.trans u v w Cu Cv Cw h₁ h₂⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isoTVia_unique_comp_transport_trans
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isoTVia_unique_comp_transport_trans (solution)
