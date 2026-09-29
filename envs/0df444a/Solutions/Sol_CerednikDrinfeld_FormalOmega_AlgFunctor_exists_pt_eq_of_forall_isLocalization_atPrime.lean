-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.AlgFunctor.exists_pt_eq_of_forall_isLocalization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/610597c6-bddf-5a1e-af11-f5d61d542b13

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime.CerednikDrinfeld.FormalOmega"

namespace CerednikDrinfeld namespace FormalOmega p2m_export "CerednikDrinfeld.FormalOmega" "AlgFunctor" namespace Scheme end CerednikDrinfeld.FormalOmega.Scheme
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalOmega" in

theorem CerednikDrinfeld.FormalOmega.Scheme.nilpPoints_exists_map_eq_of_isLocalizationAway_of_span_eq_top
    {C : Type} [CommRing C] {W : Scheme.{0}} (fW : W ⟶ Spec (CommRingCat.of C))
    (S : Type) [CommRing S] [Algebra C S] (n : ℕ) (h : Fin n → S) (hh : Ideal.span (Set.range h) = ⊤)
    (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, Algebra C (B i)]
    [∀ i, IsScalarTower C S (B i)] [∀ i, IsLocalization.Away (h i) (B i)]
    (w : ∀ i, (Scheme.nilpPoints fW).obj (B i))
    (compat : ∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra S D] [Algebra C D] [IsScalarTower C S D]
      [IsLocalization.Away (h i * h j) D] (ρ₁ : B i →ₐ[S] D) (ρ₂ : B j →ₐ[S] D),
      (Scheme.nilpPoints fW).map (ρ₁.restrictScalars C) (w i) = (Scheme.nilpPoints fW).map (ρ₂.restrictScalars C) (w j)) :
    ∃ wS : (Scheme.nilpPoints fW).obj S, ∀ i, (Scheme.nilpPoints fW).map (IsScalarTower.toAlgHom C S (B i)) wS = w i := by
  classical

  set g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of C) := Spec.map (CommRingCat.ofHom (algebraMap C S)) with hg

  have hCB : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap C (B i))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ g := by
    intro i
    rw [hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

  have hwi : ∀ i, (w i).1 ≫ fW = Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ g := by
    intro i; rw [(w i).2]; exact hCB i
  let s : ∀ i, Spec (CommRingCat.of (B i)) ⟶ Limits.pullback fW g := fun i =>
    Limits.pullback.lift (w i).1 (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) (hwi i)

  let L₂ : Fin n → Fin n → Type := fun i j => Localization.Away (h i * h j)
  let l : ∀ i j, B i →+* L₂ i j := fun i j => IsLocalization.Away.awayToAwayRight (S := B i) (h i) (h j)
  let r : ∀ i j, B j →+* L₂ i j := fun i j => IsLocalization.Away.awayToAwayLeft (S := B j) (h j) (h i)
  have hl : ∀ i j, (l i j).comp (algebraMap S (B i)) = algebraMap S (L₂ i j) := by
    intro i j; ext a; exact IsLocalization.Away.awayToAwayRight_eq (S := B i) (h i) (h j) a
  have hr : ∀ i j, (r i j).comp (algebraMap S (B j)) = algebraMap S (L₂ i j) := by
    intro i j; ext a; exact IsLocalization.Away.awayToAwayLeft_eq (S := B j) (h j) (h i) a

  let lₐ : ∀ i j, B i →ₐ[S] L₂ i j := fun i j =>
    { toRingHom := l i j, commutes' := fun a => IsLocalization.Away.awayToAwayRight_eq (S := B i) (h i) (h j) a }
  let rₐ : ∀ i j, B j →ₐ[S] L₂ i j := fun i j =>
    { toRingHom := r i j, commutes' := fun a => IsLocalization.Away.awayToAwayLeft_eq (S := B j) (h j) (h i) a }
  have hcompat : ∀ i j, Spec.map (CommRingCat.ofHom (l i j)) ≫ s i = Spec.map (CommRingCat.ofHom (r i j)) ≫ s j := by
    intro i j
    have hc := congrArg Subtype.val (compat i j (L₂ i j) (lₐ i j) (rₐ i j))
    simp only [Scheme.nilpPoints_map_val] at hc
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullback.lift_fst, s] at hc ⊢
      exact hc
    · simp only [Category.assoc, Limits.pullback.lift_snd, s]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hl, hr]
  obtain ⟨-, hex⟩ := AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
    (Limits.pullback.snd fW g) n h hh B L₂ l r hl hr
  obtain ⟨sec, hsec, hseci⟩ := hex s (fun i => Limits.pullback.lift_snd _ _ _) hcompat
  refine ⟨⟨sec ≫ Limits.pullback.fst fW g, ?_⟩, fun i => ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsec, Category.id_comp]
  · apply Subtype.ext
    simp only [Scheme.nilpPoints_map_val]
    rw [show (IsScalarTower.toAlgHom C S (B i)).toRingHom = algebraMap S (B i) from rfl, ← Category.assoc, hseci i,
      Limits.pullback.lift_fst]

theorem solution
    {C : Type} [CommRing C] (P : AlgFunctor C)

    (hsep : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A), Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (a b : P.obj A),
      (∀ i, P.map (IsScalarTower.toAlgHom C A (B i)) a = P.map (IsScalarTower.toAlgHom C A (B i)) b) → a = b)

    (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S]

    (hlfp : ∀ (g : S) (A : Type) [CommRing A] [Algebra S A] [Algebra C A] [IsScalarTower C S A] [IsLocalization.Away g A]
      [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
      (L : Type) [CommRing L] [Algebra A L] [Algebra C L] [IsScalarTower C A L] [IsLocalization.AtPrime L 𝔭] (a b : P.obj A),
      P.map (IsScalarTower.toAlgHom C A L) a = P.map (IsScalarTower.toAlgHom C A L) b →
      ∃ (f : A) (_ : f ∉ 𝔭) (Af : Type) (_ : CommRing Af) (_ : Algebra A Af) (_ : Algebra C Af) (_ : IsScalarTower C A Af)
        (_ : IsLocalization.Away f Af),
        P.map (IsScalarTower.toAlgHom C A Af) a = P.map (IsScalarTower.toAlgHom C A Af) b)

    {W : Scheme.{0}} (fW : W ⟶ Spec (CommRingCat.of C)) (hW : LocallyOfFiniteType fW)
    (pt : ∀ (T : Type) [CommRing T] [Algebra C T], (Scheme.nilpPoints fW).obj T → P.obj T)
    (hnat : ∀ (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
      (w : (Scheme.nilpPoints fW).obj T), pt T' ((Scheme.nilpPoints fW).map φ w) = P.map φ (pt T w))
    (hinj : ∀ (T : Type) [CommRing T] [Algebra C T] [IsNoetherianRing T]
      (w w' : (Scheme.nilpPoints fW).obj T), pt T w = pt T w' → w = w')

    (x : P.obj S)
    (hloc : ∀ (𝔭 : Ideal S) [𝔭.IsPrime] (L : Type) [CommRing L] [Algebra S L] [Algebra C L] [IsScalarTower C S L]
      [IsLocalization.AtPrime L 𝔭],
      ∃ w : (Scheme.nilpPoints fW).obj L, pt L w = P.map (IsScalarTower.toAlgHom C S L) x) :
    ∃ w : (Scheme.nilpPoints fW).obj S, pt S w = x := by
  classical

  have hspread : ∀ (𝔭 : Ideal S) [𝔭.IsPrime], ∃ (g : S), g ∉ 𝔭 ∧
      ∃ (w : (Scheme.nilpPoints fW).obj (Localization.Away g)) (𝔮 : Ideal (Localization.Away g)) (_ : 𝔮.IsPrime),
        𝔮.comap (algebraMap S (Localization.Away g)) = 𝔭 ∧
        P.map (IsScalarTower.toAlgHom C (Localization.Away g) (Localization.AtPrime 𝔮)) (pt (Localization.Away g) w) =
          P.map (IsScalarTower.toAlgHom C (Localization.Away g) (Localization.AtPrime 𝔮))
            (P.map (IsScalarTower.toAlgHom C S (Localization.Away g)) x) := by
    intro 𝔭 h𝔭
    haveI : LocallyOfFiniteType fW := hW

    obtain ⟨w₀, hw₀⟩ := hloc 𝔭 (Localization.AtPrime 𝔭)
    let x𝔭 : ↥(Spec (CommRingCat.of S)) := (⟨𝔭, h𝔭⟩ : PrimeSpectrum S)
    let e := StructureSheaf.stalkIso S x𝔭
    let sX : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of C) := Spec.map (CommRingCat.ofHom (algebraMap C S))
    let eR : Localization.AtPrime 𝔭 →+* ↑((structurePresheafInCommRingCat S).stalk x𝔭) :=
      e.toAlgHom.toRingHom
    let φ := Spec.map (CommRingCat.ofHom eR) ≫ w₀.1
    have hring : CommRingCat.ofHom (algebraMap C (Localization.AtPrime 𝔭)) ≫ CommRingCat.ofHom eR =
        CommRingCat.ofHom (algebraMap C S) ≫ StructureSheaf.toStalk S x𝔭 := by
      apply CommRingCat.hom_ext
      ext c
      show e (algebraMap C (Localization.AtPrime 𝔭) c) = (StructureSheaf.toStalk S x𝔭).hom (algebraMap C S c)
      rw [IsScalarTower.algebraMap_apply C S (Localization.AtPrime 𝔭) c, AlgEquiv.commutes]
      rfl
    have hφ : φ ≫ fW = (Spec (CommRingCat.of S)).fromSpecStalk x𝔭 ≫ sX := by
      rw [Spec.fromSpecStalk_eq']
      show (Spec.map (CommRingCat.ofHom eR) ≫ w₀.1) ≫ fW =
        Spec.map (StructureSheaf.toStalk S x𝔭) ≫ Spec.map (CommRingCat.ofHom (algebraMap C S))
      rw [Category.assoc, w₀.2, ← Spec.map_comp, hring, Spec.map_comp]
    obtain ⟨U, hxU, f, hf₁, hf₂⟩ := spread_out_of_isGermInjective' sX fW φ hφ

    obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    have hg : g ∉ 𝔭 := by
      have hxg' := hxg
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hxg'
      exact hxg'

    let ιg : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec (CommRingCat.of S) :=
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
    have hrange : Set.range ιg ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      apply hgU
      show PrimeSpectrum.comap (algebraMap S (Localization.Away g)) y ∈ PrimeSpectrum.basicOpen g
      rw [PrimeSpectrum.mem_basicOpen]
      exact fun hmem => y.2.ne_top (y.asIdeal.eq_top_of_isUnit_mem hmem (IsLocalization.Away.algebraMap_isUnit g))
    let k : Spec (CommRingCat.of (Localization.Away g)) ⟶ U := IsOpenImmersion.lift U.ι ιg hrange
    have hk : k ≫ U.ι = ιg := IsOpenImmersion.lift_fac _ _ _
    let w : (Scheme.nilpPoints fW).obj (Localization.Away g) := ⟨k ≫ f, by
      rw [Category.assoc, hf₂, ← Category.assoc, hk]
      show ιg ≫ sX = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]⟩

    have hdisj : Disjoint ((Submonoid.powers g : Submonoid S) : Set S) ↑𝔭 :=
      Set.disjoint_left.mpr (by rintro a ⟨m, rfl⟩ ha; exact hg (h𝔭.mem_of_pow_mem m ha))
    let 𝔮 : Ideal (Localization.Away g) := Ideal.map (algebraMap S (Localization.Away g)) 𝔭
    haveI h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ 𝔭 h𝔭 hdisj
    have hcomap : 𝔮.comap (algebraMap S (Localization.Away g)) = 𝔭 :=
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) _ h𝔭 hdisj
    refine ⟨g, hg, w, 𝔮, h𝔮, hcomap, ?_⟩

    haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) 𝔭 := by
      have hinst : IsLocalization ((𝔮.comap (algebraMap S (Localization.Away g))).primeCompl) (Localization.AtPrime 𝔮) :=
        (inferInstance : IsLocalization.AtPrime (Localization.AtPrime 𝔮) (𝔮.comap (algebraMap S (Localization.Away g))))
      have hM : (𝔮.comap (algebraMap S (Localization.Away g))).primeCompl = 𝔭.primeCompl :=
        Submonoid.ext fun y => by
          show y ∈ ((↑(𝔮.comap (algebraMap S (Localization.Away g))) : Set S)ᶜ) ↔ y ∈ ((↑𝔭 : Set S)ᶜ)
          rw [hcomap]
      show IsLocalization 𝔭.primeCompl (Localization.AtPrime 𝔮)
      rw [← hM]
      exact hinst
    let j : Localization.AtPrime 𝔮 ≃ₐ[S] Localization.AtPrime 𝔭 :=
      IsLocalization.algEquiv 𝔭.primeCompl (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔭)
    let jC : Localization.AtPrime 𝔮 →ₐ[C] Localization.AtPrime 𝔭 := j.toAlgHom.restrictScalars C
    let ψ : Localization.Away g →ₐ[C] Localization.AtPrime 𝔭 :=
      jC.comp (IsScalarTower.toAlgHom C (Localization.Away g) (Localization.AtPrime 𝔮))
    have hψS : ∀ s' : S, ψ (algebraMap S (Localization.Away g) s') = algebraMap S (Localization.AtPrime 𝔭) s' := by
      intro s'
      show j (algebraMap (Localization.Away g) (Localization.AtPrime 𝔮) (algebraMap S (Localization.Away g) s')) = _
      rw [← IsScalarTower.algebraMap_apply S (Localization.Away g) (Localization.AtPrime 𝔮) s', AlgEquiv.commutes]

    have hw₀1 : w₀.1 = Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ φ := by
      show w₀.1 = Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom eR) ≫ w₀.1
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        show e.symm.toAlgHom.toRingHom.comp eR = RingHom.id _ from RingHom.ext fun y => e.symm_apply_apply y,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    have hkk : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ k =
        Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ U.fromSpecStalkOfMem x𝔭 hxU := by
      have hU : U.fromSpecStalkOfMem x𝔭 hxU ≫ U.ι = Spec.map (StructureSheaf.toStalk S x𝔭) :=
        (Scheme.Opens.fromSpecStalkOfMem_ι U x𝔭 hxU).trans (Spec.fromSpecStalk_eq' _ _)
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hk]
      erw [hU]
      show Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) =
        Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ Spec.map (StructureSheaf.toStalk S x𝔭)
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_hom (StructureSheaf.toStalk S x𝔭),
        ← CommRingCat.ofHom_comp]
      congr 2
      ext s'
      show ψ (algebraMap S (Localization.Away g) s') = e.symm ((StructureSheaf.toStalk S x𝔭).hom s')
      rw [hψS, show (StructureSheaf.toStalk S x𝔭).hom s' = algebraMap S _ s' from rfl, AlgEquiv.commutes]
    have hkey : (Scheme.nilpPoints fW).map ψ w = w₀ := by
      apply Subtype.ext
      rw [Scheme.nilpPoints_map_val]
      show Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ k ≫ f = w₀.1
      rw [hw₀1, hf₁, ← Category.assoc, hkk]
      exact Category.assoc _ _ _

    have hinjj : ∀ a b : P.obj (Localization.AtPrime 𝔮), P.map jC a = P.map jC b → a = b := by
      intro a b hab
      have h' := congrArg (P.map (j.symm.toAlgHom.restrictScalars C)) hab
      rwa [← P.map_comp, ← P.map_comp,
        show (j.symm.toAlgHom.restrictScalars C).comp jC = AlgHom.id C _ from
          AlgHom.ext fun y => j.symm_apply_apply y, P.map_id, P.map_id] at h'
    apply hinjj
    rw [← P.map_comp, ← P.map_comp, ← hnat, hkey, hw₀, ← P.map_comp]
    congr 1
    apply AlgHom.ext
    intro s'
    exact (hψS s').symm

  have hsec : ∀ (𝔭 : Ideal S) [𝔭.IsPrime], ∃ (hS : S), hS ∉ 𝔭 ∧
      ∃ (B : Type) (_ : CommRing B) (_ : Algebra S B) (_ : Algebra C B) (_ : IsScalarTower C S B)
        (_ : IsLocalization.Away hS B) (w : (Scheme.nilpPoints fW).obj B),
        pt B w = P.map (IsScalarTower.toAlgHom C S B) x := by
    intro 𝔭 _
    obtain ⟨g, hg, w, 𝔮, h𝔮, hcomap, hagree⟩ := hspread 𝔭
    haveI := h𝔮
    obtain ⟨f, hf, Af, iAf1, iAf2, iAf3, iAf4, iAf5, hAf⟩ :=
      hlfp g (Localization.Away g) 𝔮 (Localization.AtPrime 𝔮) (pt (Localization.Away g) w)
        (P.map (IsScalarTower.toAlgHom C S (Localization.Away g)) x) hagree
    letI : Algebra S Af := ((algebraMap (Localization.Away g) Af).comp (algebraMap S (Localization.Away g))).toAlgebra
    haveI : IsScalarTower S (Localization.Away g) Af := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower C S Af := IsScalarTower.of_algebraMap_eq (fun c => by
      rw [IsScalarTower.algebraMap_apply C (Localization.Away g) Af c,
        IsScalarTower.algebraMap_apply C S (Localization.Away g) c]
      rfl)

    obtain ⟨k, s, hs⟩ := IsLocalization.Away.surj g f
    have hunit : IsUnit (algebraMap (Localization.Away g) Af (algebraMap S (Localization.Away g) g ^ k)) :=
      ((IsLocalization.Away.algebraMap_isUnit g).pow k).map _
    haveI hAway1 : IsLocalization.Away (algebraMap S (Localization.Away g) s) Af := by
      rw [← hs]
      exact IsLocalization.Away.mul_of_isUnit f (algebraMap S (Localization.Away g) g ^ k) hunit
    haveI hAway2 : IsLocalization.Away (s * g) Af := IsLocalization.Away.mul (Localization.Away g) Af g s
    have hgq : algebraMap S (Localization.Away g) g ∉ 𝔮 := fun hmem =>
      h𝔮.ne_top (𝔮.eq_top_of_isUnit_mem hmem (IsLocalization.Away.algebraMap_isUnit g))
    have hs𝔭 : s * g ∉ 𝔭 := by
      intro hmem
      rw [← hcomap, Ideal.mem_comap, map_mul] at hmem
      rcases h𝔮.mem_or_mem hmem with hsq | hgq'
      · rw [← hs] at hsq
        rcases h𝔮.mem_or_mem hsq with hfq | hgk
        · exact hf hfq
        · exact hgq (h𝔮.mem_of_pow_mem k hgk)
      · exact hgq hgq'
    refine ⟨s * g, hs𝔭, Af, iAf1, inferInstance, iAf3, inferInstance, hAway2,
      (Scheme.nilpPoints fW).map (IsScalarTower.toAlgHom C (Localization.Away g) Af) w, ?_⟩
    rw [hnat, hAf, ← P.map_comp]
    rfl

  have htop : Ideal.span {hS : S | ∃ (B : Type) (_ : CommRing B) (_ : Algebra S B) (_ : Algebra C B) (_ : IsScalarTower C S B)
      (_ : IsLocalization.Away hS B) (w : (Scheme.nilpPoints fW).obj B), pt B w = P.map (IsScalarTower.toAlgHom C S B) x} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI : 𝔪.IsPrime := h𝔪.isPrime
    obtain ⟨hS, hnot, hex⟩ := hsec 𝔪
    exact hnot (hle (Ideal.subset_span hex))
  obtain ⟨F, hFT, h1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp htop)
  have hrange : Set.range (fun i : Fin F.card => ((F.equivFin.symm i) : S)) = ↑F := by
    ext y; constructor
    · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
    · intro hy; exact ⟨F.equivFin ⟨y, hy⟩, by simp⟩
  have hh : Ideal.span (Set.range (fun i : Fin F.card => ((F.equivFin.symm i) : S))) = ⊤ := by
    rw [hrange]; exact (Ideal.eq_top_iff_one _).mpr h1
  have hmem : ∀ i : Fin F.card, ∃ (B : Type) (_ : CommRing B) (_ : Algebra S B) (_ : Algebra C B) (_ : IsScalarTower C S B)
      (_ : IsLocalization.Away ((F.equivFin.symm i) : S) B) (w : (Scheme.nilpPoints fW).obj B),
      pt B w = P.map (IsScalarTower.toAlgHom C S B) x := fun i => hFT (F.equivFin.symm i).2
  choose B iB₁ iB₂ iB₃ iB₄ iB₅ w hw using hmem

  have hx : ∀ (k : Fin F.card) (D : Type) [CommRing D] [Algebra S D] [Algebra C D] [IsScalarTower C S D] (ρ : B k →ₐ[S] D),
      P.map (ρ.restrictScalars C) (P.map (IsScalarTower.toAlgHom C S (B k)) x) = P.map (IsScalarTower.toAlgHom C S D) x := by
    intro k D _ _ _ _ ρ
    rw [← P.map_comp]
    congr 1
    apply AlgHom.ext
    intro y
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.toAlgHom_apply, AlgHom.commutes]

  have hcompat : ∀ (i j : Fin F.card) (D : Type) [CommRing D] [Algebra S D] [Algebra C D] [IsScalarTower C S D]
      [IsLocalization.Away (((F.equivFin.symm i) : S) * ((F.equivFin.symm j) : S)) D] (ρ₁ : B i →ₐ[S] D) (ρ₂ : B j →ₐ[S] D),
      (Scheme.nilpPoints fW).map (ρ₁.restrictScalars C) (w i) = (Scheme.nilpPoints fW).map (ρ₂.restrictScalars C) (w j) := by
    intro i j D _ _ _ _ _ ρ₁ ρ₂
    haveI : IsNoetherianRing D :=
      IsLocalization.isNoetherianRing (Submonoid.powers (((F.equivFin.symm i) : S) * ((F.equivFin.symm j) : S))) D inferInstance
    apply hinj D
    rw [hnat, hnat, hw i, hw j, hx i D ρ₁, hx j D ρ₂]

  obtain ⟨wS, hwS⟩ := CerednikDrinfeld.FormalOmega.Scheme.nilpPoints_exists_map_eq_of_isLocalizationAway_of_span_eq_top
    fW S F.card (fun i : Fin F.card => ((F.equivFin.symm i) : S)) hh B w hcompat
  refine ⟨wS, hsep S F.card (fun i : Fin F.card => ((F.equivFin.symm i) : S)) hh B _ _ ?_⟩
  intro i
  rw [← hnat, hwS i, hw i]

end S_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime (solution)
