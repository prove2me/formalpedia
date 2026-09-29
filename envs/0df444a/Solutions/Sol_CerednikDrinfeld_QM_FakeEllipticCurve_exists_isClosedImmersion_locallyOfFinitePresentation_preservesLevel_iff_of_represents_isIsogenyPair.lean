-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClosedImmersion_locallyOfFinitePresentation_preservesLevel_iff_of_represents_isIsogenyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/70f96459-445e-5f37-8f06-f23d7aaa6dce

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_locallyOfFinitePresentation_preservesLevel_iff_of_represents_isIsogenyPair
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
open CategoryTheory.Limits

namespace P3bS14

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem specMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem specMap_id (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (CommRingCat.of R)) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem exists_eq_specMap {R S : Type} [CommRing R] [CommRing S]
    (z : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) :
    ∃ ψ : R →+* S, Spec.map (CommRingCat.ofHom ψ) = z := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective z
  exact ⟨φ.hom, by rw [CommRingCat.ofHom_hom]⟩

theorem ringHom_eq_of_specMap_eq {R S : Type} [CommRing R] [CommRing S] (φ ψ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  rwa [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at this

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem ptext {S₁ : Type} [CommRing S₁] {X Y Z : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of S₁)} {gg : X ⟶ Y} {fY : Y ⟶ Z}
    {s : Spec (CommRingCat.of S₁) ⟶ Z} (hsq : CategoryTheory.IsPullback gg fX fY s)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S₁)} (P Q : SchemeHomOver t fX) (h : P.1 ≫ gg = Q.1 ≫ gg) : P = Q :=
  Subtype.ext (hsq.hom_ext h (by rw [P.2, Q.2]))

theorem ideal_eq_bot_of_forall_map_away_eq_bot {A₀ : Type} [CommRing A₀] (J : Ideal A₀)
    {ι : Type} (rr : ι → A₀) (hr : Ideal.span (Set.range rr) = ⊤)
    (h : ∀ i, J.map (algebraMap A₀ (Localization.Away (rr i))) = ⊥) : J = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have hx0 : ∀ i, ∃ n : ℕ, rr i ^ n * x = 0 := by
    intro i
    have h0 : algebraMap A₀ (Localization.Away (rr i)) x = 0 := by
      have hm : algebraMap A₀ (Localization.Away (rr i)) x ∈ J.map (algebraMap A₀ (Localization.Away (rr i))) :=
        Ideal.mem_map_of_mem _ hx
      rw [h i] at hm
      simpa using hm
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (rr i))] at h0
    obtain ⟨⟨m, ⟨n, rfl⟩⟩, hm⟩ := h0
    exact ⟨n, by simpa using hm⟩
  have hmem : x ∈ (⊥ : Submodule A₀ A₀) :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem ⊥ (Set.range rr) hr x (by
      rintro ⟨_, i, rfl⟩
      obtain ⟨n, hn⟩ := hx0 i
      exact ⟨n, by simpa [smul_eq_mul] using hn⟩)
  simpa using hmem

theorem isPullbackVia_id {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hid]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · intro T t' P Q
    have key : ∀ {t'' : T ⟶ Spec (CommRingCat.of S)} (_ : t' = t'') (P' Q' : SchemeHomOver t'' E.f),
        P'.1 = P.1 → Q'.1 = Q.1 → (E.L.mul t' P Q).1 ≫ 𝟙 E.A = (E.L.mul t'' P' Q').1 := by
      rintro t'' rfl P' Q' hP hQ
      obtain rfl : P' = P := Subtype.ext hP
      obtain rfl : Q' = Q := Subtype.ext hQ
      exact Category.comp_id _
    exact key (by rw [hid, Category.comp_id]) _ _ (by simp) (by simp)
  · intro x; simp
  · intro T t' P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by simpa using h⟩

theorem exists_presentation {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (E : FakeEllipticCurve Λ N S) :
    ∃ (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A), FakeEllipticCurve.IsPullbackVia φ E E' g := by
  obtain ⟨E', g, hg, hmul, hact, hlev, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff φ E
  exact ⟨E', g, hg, hmul, hact, hlev⟩

theorem lev_converse {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (h : FakeEllipticCurve.IsPullbackVia φ E E' g)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f)
    (hP : ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) : FactorsThrough E'.lev P := by
  obtain ⟨hg, hmul, -, hlev⟩ := h
  exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback φ E E' g hg hmul hlev t' P hP

theorem exists_comparison {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (E : FakeEllipticCurve Λ N S)
    (E₁ E₂ : FakeEllipticCurve Λ N S') (g₁ : E₁.A ⟶ E.A) (h₁ : FakeEllipticCurve.IsPullbackVia φ E E₁ g₁)
    (g₂ : E₂.A ⟶ E.A) (h₂ : FakeEllipticCurve.IsPullbackVia φ E E₂ g₂) :
    ∃ k : E₂.A ⟶ E₁.A, k ≫ g₁ = g₂ ∧ FakeEllipticCurve.IsPullbackVia (RingHom.id S') E₁ E₂ k := by
  obtain ⟨k, hkg, -, -, hk⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq φ (RingHom.id S') φ
      (RingHom.id_comp φ) E E₁ E₂ g₁ h₁ (fun t' P hP => lev_converse φ E E₁ g₁ h₁ t' P hP) g₂ h₂
  exact ⟨k, hkg, hk⟩

structure Pair (r d : ℕ) {T : Type} [CommRing T] (E' A' : FakeEllipticCurve Λ N T) where
  φ : E'.A ⟶ A'.A
  φ' : A'.A ⟶ E'.A
  hφ : φ ≫ A'.f = E'.f
  hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ'

theorem Pair.ext' {r d : ℕ} {T : Type} [CommRing T] {E' A' : FakeEllipticCurve Λ N T} (p q : Pair r d E' A')
    (h : p.φ = q.φ) (h' : p.φ' = q.φ') : p = q := by
  cases p; cases q; cases h; cases h'; rfl

def Pair.PL {r d : ℕ} {T : Type} [CommRing T] {E' A' : FakeEllipticCurve Λ N T} (q : Pair r d E' A') : Prop :=
  FakeEllipticCurve.PreservesLevel E' A' q.φ q.hφ

theorem exists_pullPair {U D : Type} [CommRing U] [CommRing D] (p : U →+* D)
    (dd : ℕ) (E' A' : FakeEllipticCurve Λ N U) (E'' A'' : FakeEllipticCurve Λ N D)
    (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia p E' E'' hE)
    (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia p A' A'' hA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair dd E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ) :
    ∃ (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f),
      FakeEllipticCurve.IsIsogenyPair dd E'' A'' ψ ψ' ∧ FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ ∧
        ψ ≫ hA = hE ≫ φ ∧ ψ' ≫ hE = hA ≫ φ' := by
  have hhA₀ := hhA
  obtain ⟨hsqE, Emul, Eact, Elev⟩ := hhE
  obtain ⟨hsqA, Amul, Aact, Alev⟩ := hhA
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := hp
  let ψ : E''.A ⟶ A''.A := hsqA.lift (hE ≫ φ) E''.f (by rw [Category.assoc, hφo]; exact hsqE.w)
  have hψ₁ : ψ ≫ hA = hE ≫ φ := hsqA.lift_fst _ _ _
  have hψ₂ : ψ ≫ A''.f = E''.f := hsqA.lift_snd _ _ _
  let ψ' : A''.A ⟶ E''.A := hsqE.lift (hA ≫ φ') A''.f (by rw [Category.assoc, hφ'o]; exact hsqA.w)
  have hψ'₁ : ψ' ≫ hE = hA ≫ φ' := hsqE.lift_fst _ _ _
  have hψ'₂ : ψ' ≫ E''.f = A''.f := hsqE.lift_snd _ _ _
  have ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t E''.f),
      mapPt ψ hψ₂ (E''.L.mul t P Q) = A''.L.mul t (mapPt ψ hψ₂ P) (mapPt ψ hψ₂ Q) := by
    intro T t P Q
    apply ptext hsqA
    rw [mapPt_coe, Category.assoc, hψ₁, ← Category.assoc, Emul, Amul]
    have := congrArg Subtype.val (hφmul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr A'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ₁])
      (by simp only [mapPt_coe, Category.assoc, hψ₁])
  have ψ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t A''.f),
      mapPt ψ' hψ'₂ (A''.L.mul t P Q) = E''.L.mul t (mapPt ψ' hψ'₂ P) (mapPt ψ' hψ'₂ Q) := by
    intro T t P Q
    apply ptext hsqE
    rw [mapPt_coe, Category.assoc, hψ'₁, ← Category.assoc, Amul, Emul]
    have := congrArg Subtype.val (hφ'mul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr E'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ'₁])
      (by simp only [mapPt_coe, Category.assoc, hψ'₁])
  have ψ_act : ∀ x : ↥Λ, E''.act x ≫ ψ = ψ ≫ A''.act x := by
    intro x
    apply hsqA.hom_ext
    · rw [Category.assoc, hψ₁, ← Category.assoc, Eact, Category.assoc, hφlin, Category.assoc, Aact, ← Category.assoc ψ hA, hψ₁,
        Category.assoc]
    · rw [Category.assoc, hψ₂, E''.act_over, Category.assoc, A''.act_over, hψ₂]
  have ψ'_act : ∀ x : ↥Λ, A''.act x ≫ ψ' = ψ' ≫ E''.act x := by
    intro x
    apply hsqE.hom_ext
    · rw [Category.assoc, hψ'₁, ← Category.assoc, Aact, Category.assoc, hφ'lin, Category.assoc, Eact, ← Category.assoc ψ' hE, hψ'₁,
        Category.assoc]
    · rw [Category.assoc, hψ'₂, A''.act_over, Category.assoc, E''.act_over, hψ'₂]
  have ψ_deg : ∀ hm : (((dd : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      ψ ≫ ψ' = E''.act ⟨_, hm⟩ ∧ ψ' ≫ ψ = A''.act ⟨_, hm⟩ := by
    intro hm
    obtain ⟨h1, h2⟩ := hdeg hm
    constructor
    · apply hsqE.hom_ext
      · rw [Category.assoc, hψ'₁, ← Category.assoc, hψ₁, Category.assoc, h1, Eact]
      · rw [Category.assoc, hψ'₂, hψ₂, E''.act_over]
    · apply hsqA.hom_ext
      · rw [Category.assoc, hψ₁, ← Category.assoc, hψ'₁, Category.assoc, h2, Aact]
      · rw [Category.assoc, hψ₂, hψ'₂, A''.act_over]
  have ψ_lev : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ₂ := by
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := Elev t P hP
    have hQ := hl (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    obtain ⟨Q₀, hQ₀⟩ := hQ
    apply lev_converse p A' A'' hA hhA₀ t (mapPt ψ hψ₂ P)
    exact ⟨Q₀, by rw [hQ₀]; simp only [mapPt_coe, Category.assoc, hψ₁]⟩
  exact ⟨ψ, ψ', hψ₂, ⟨hψ₂, hψ'₂, ψ_hom, ψ'_hom, ψ_act, ψ'_act, ψ_deg⟩, ψ_lev, hψ₁, hψ'₁⟩

theorem exists_pullPair₀ {r d : ℕ} {U D : Type} [CommRing U] [CommRing D] (p : U →+* D)
    (E' A' : FakeEllipticCurve Λ N U) (E'' A'' : FakeEllipticCurve Λ N D)
    (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia p E' E'' hE)
    (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia p A' A'' hA) (q : Pair r d E' A') :
    ∃ q'' : Pair r d E'' A'', q''.φ ≫ hA = hE ≫ q.φ ∧ q''.φ' ≫ hE = hA ≫ q.φ' := by
  obtain ⟨hsqE, Emul, Eact, -⟩ := hhE
  obtain ⟨hsqA, Amul, Aact, -⟩ := hhA
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := q.hp

  let ψ : E''.A ⟶ A''.A := hsqA.lift (hE ≫ q.φ) E''.f (by rw [Category.assoc, hφo]; exact hsqE.w)
  have hψ₁ : ψ ≫ hA = hE ≫ q.φ := hsqA.lift_fst _ _ _
  have hψ₂ : ψ ≫ A''.f = E''.f := hsqA.lift_snd _ _ _
  let ψ' : A''.A ⟶ E''.A := hsqE.lift (hA ≫ q.φ') A''.f (by rw [Category.assoc, hφ'o]; exact hsqA.w)
  have hψ'₁ : ψ' ≫ hE = hA ≫ q.φ' := hsqE.lift_fst _ _ _
  have hψ'₂ : ψ' ≫ E''.f = A''.f := hsqE.lift_snd _ _ _
  have ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t E''.f),
      mapPt ψ hψ₂ (E''.L.mul t P Q) = A''.L.mul t (mapPt ψ hψ₂ P) (mapPt ψ hψ₂ Q) := by
    intro T t P Q
    apply ptext hsqA
    rw [mapPt_coe, Category.assoc, hψ₁, ← Category.assoc, Emul, Amul]
    have := congrArg Subtype.val (hφmul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr A'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ₁])
      (by simp only [mapPt_coe, Category.assoc, hψ₁])
  have ψ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of D)) (P Q : SchemeHomOver t A''.f),
      mapPt ψ' hψ'₂ (A''.L.mul t P Q) = E''.L.mul t (mapPt ψ' hψ'₂ P) (mapPt ψ' hψ'₂ Q) := by
    intro T t P Q
    apply ptext hsqE
    rw [mapPt_coe, Category.assoc, hψ'₁, ← Category.assoc, Amul, Emul]
    have := congrArg Subtype.val (hφ'mul (t ≫ Spec.map (CommRingCat.ofHom p))
      ⟨P.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ hA, by rw [Category.assoc, hsqA.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr E'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hψ'₁])
      (by simp only [mapPt_coe, Category.assoc, hψ'₁])
  have ψ_act : ∀ x : ↥Λ, E''.act x ≫ ψ = ψ ≫ A''.act x := by
    intro x
    apply hsqA.hom_ext
    · rw [Category.assoc, hψ₁, ← Category.assoc, Eact, Category.assoc, hφlin, Category.assoc, Aact, ← Category.assoc ψ hA, hψ₁,
        Category.assoc]
    · rw [Category.assoc, hψ₂, E''.act_over, Category.assoc, A''.act_over, hψ₂]
  have ψ'_act : ∀ x : ↥Λ, A''.act x ≫ ψ' = ψ' ≫ E''.act x := by
    intro x
    apply hsqE.hom_ext
    · rw [Category.assoc, hψ'₁, ← Category.assoc, Aact, Category.assoc, hφ'lin, Category.assoc, Eact, ← Category.assoc ψ' hE, hψ'₁,
        Category.assoc]
    · rw [Category.assoc, hψ'₂, A''.act_over, Category.assoc, E''.act_over, hψ'₂]
  have ψ_deg : ∀ hm : ((((r ^ d : ℕ) : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      ψ ≫ ψ' = E''.act ⟨_, hm⟩ ∧ ψ' ≫ ψ = A''.act ⟨_, hm⟩ := by
    intro hm
    obtain ⟨h1, h2⟩ := hdeg hm
    constructor
    · apply hsqE.hom_ext
      · rw [Category.assoc, hψ'₁, ← Category.assoc, hψ₁, Category.assoc, h1, Eact]
      · rw [Category.assoc, hψ'₂, hψ₂, E''.act_over]
    · apply hsqA.hom_ext
      · rw [Category.assoc, hψ₁, ← Category.assoc, hψ'₁, Category.assoc, h2, Aact]
      · rw [Category.assoc, hψ₂, hψ'₂, A''.act_over]
  exact ⟨⟨ψ, ψ', hψ₂, ⟨hψ₂, hψ'₂, ψ_hom, ψ'_hom, ψ_act, ψ'_act, ψ_deg⟩⟩, hψ₁, hψ'₁⟩

theorem PL_pull {r d : ℕ} {U D : Type} [CommRing U] [CommRing D] (p : U →+* D)
    (E' A' : FakeEllipticCurve Λ N U) (E'' A'' : FakeEllipticCurve Λ N D)
    (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia p E' E'' hE)
    (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia p A' A'' hA) (q : Pair r d E' A')
    (q'' : Pair r d E'' A'') (h1 : q''.φ ≫ hA = hE ≫ q.φ) (hq : q.PL) : q''.PL := by
  obtain ⟨hsqE, -, -, Elev⟩ := hhE
  intro T t P hP
  obtain ⟨P₀, hP₀⟩ := Elev t P hP
  obtain ⟨Q₀, hQ₀⟩ := hq (t ≫ Spec.map (CommRingCat.ofHom p))
    ⟨P.1 ≫ hE, by rw [Category.assoc, hsqE.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
  apply lev_converse p A' A'' hA hhA t (mapPt q''.φ q''.hφ P)
  exact ⟨Q₀, by rw [hQ₀]; simp only [mapPt_coe, Category.assoc, h1]⟩

section Contract

variable {r d : ℕ} {S : Type} [CommRing S] {E A : FakeEllipticCurve Λ N S}
  {Z : Scheme.{0}} {ζ : Z ⟶ Spec (CommRingCat.of S)}

abbrev PtZ (r d : ℕ) (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S) (Z : Scheme.{0})
    (ζ : Z ⟶ Spec (CommRingCat.of S)) : Type 1 :=
  ∀ (T : Type) [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
    FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ

variable (pt : PtZ r d S E A Z ζ)

def ptP {T : Type} [CommRing T] (ρ : S →+* T)
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia ρ E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia ρ A A' gA) (q : Pair r d E' A') :
    Spec (CommRingCat.of T) ⟶ Z :=
  letI : Algebra S T := ρ.toAlgebra
  (pt T E' A' gE hgE gA hgA q.φ q.φ' q.hφ q.hp).1

theorem ptP_over {T : Type} [CommRing T] (ρ : S →+* T)
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia ρ E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia ρ A A' gA) (q : Pair r d E' A') :
    ptP pt ρ E' A' gE hgE gA hgA q ≫ ζ = Spec.map (CommRingCat.ofHom ρ) :=
  letI : Algebra S T := ρ.toAlgebra
  (pt T E' A' gE hgE gA hgA q.φ q.φ' q.hφ q.hp).2

theorem ptP_congr {T : Type} [CommRing T] {ρ₁ ρ₂ : S →+* T}
    (hρ : ρ₁ = ρ₂) (E' A' : FakeEllipticCurve Λ N T) {gE₁ gE₂ : E'.A ⟶ E.A} (hgE12 : gE₁ = gE₂)
    {gA₁ gA₂ : A'.A ⟶ A.A} (hgA12 : gA₁ = gA₂)
    (h₁E : FakeEllipticCurve.IsPullbackVia ρ₁ E E' gE₁) (h₁A : FakeEllipticCurve.IsPullbackVia ρ₁ A A' gA₁)
    (h₂E : FakeEllipticCurve.IsPullbackVia ρ₂ E E' gE₂) (h₂A : FakeEllipticCurve.IsPullbackVia ρ₂ A A' gA₂)
    {q₁ q₂ : Pair r d E' A'} (hq : q₁ = q₂) :
    ptP pt ρ₁ E' A' gE₁ h₁E gA₁ h₁A q₁ = ptP pt ρ₂ E' A' gE₂ h₂E gA₂ h₂A q₂ := by
  subst hρ hgE12 hgA12 hq; rfl

theorem pt_inst_congr {T : Type} [CommRing T]
    (i₁ i₂ : Algebra S T) (h : i₁ = i₂) (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (gA : A'.A ⟶ A.A)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    (h₁E : letI := i₁; FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (h₁A : letI := i₁; FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (h₂E : letI := i₂; FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (h₂A : letI := i₂; FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA) :
    (@pt T _ i₁ E' A' gE h₁E gA h₁A φ φ' hφ hp).1 = (@pt T _ i₂ E' A' gE h₂E gA h₂A φ φ' hφ hp).1 := by
  subst h; rfl

theorem pt_eq_ptP {T : Type} [CommRing T] [i : Algebra S T]
    (ρ : S →+* T) (hρ : algebraMap S T = ρ)
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    (hgE' : FakeEllipticCurve.IsPullbackVia ρ E E' gE) (hgA' : FakeEllipticCurve.IsPullbackVia ρ A A' gA) :
    (pt T E' A' gE hgE gA hgA φ φ' hφ hp).1 = ptP pt ρ E' A' gE hgE' gA hgA' ⟨φ, φ', hφ, hp⟩ := by
  subst hρ
  have hi : i = (algebraMap S T).toAlgebra := Algebra.algebra_ext _ _ (fun _ => rfl)
  exact pt_inst_congr pt i (algebraMap S T).toAlgebra hi E' A' gE gA φ φ' hφ hp hgE hgA hgE' hgA'

def NatZ : Prop :=
  ∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
    (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
    (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
    (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
    (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
    (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ'),
    ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
      (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq).1 =
        Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (pt T E' A' gE hgE gA hgA φ φ' hφ hp).1

def SurjZ : Prop :=
  ∀ (T : Type) [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ),
    ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ'),
      pt T E' A' gE hgE gA hgA φ φ' hφ hp = z

def InjZ : Prop :=
  ∀ (T : Type) [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
    (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
    (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
    (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂'),
    pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ = pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ → φ₁ = φ₂ ∧ φ₁' = φ₂'

variable {pt}

theorem X2R (hn : NatZ pt)
    {T T' : Type} [CommRing T] [CommRing T'] (ρ : S →+* T) (χ : T →+* T')
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia ρ E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia ρ A A' gA) (q : Pair r d E' A')
    (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia χ E' E'' hE)
    (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia χ A' A'' hA)
    (hgE'' : FakeEllipticCurve.IsPullbackVia (χ.comp ρ) E E'' (hE ≫ gE))
    (hgA'' : FakeEllipticCurve.IsPullbackVia (χ.comp ρ) A A'' (hA ≫ gA))
    (q'' : Pair r d E'' A'') (h1 : q''.φ ≫ hA = hE ≫ q.φ) (h2 : q''.φ' ≫ hE = hA ≫ q.φ') :
    ptP pt (χ.comp ρ) E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' q'' =
      Spec.map (CommRingCat.ofHom χ) ≫ ptP pt ρ E' A' gE hgE gA hgA q := by
  letI i₁ : Algebra S T := ρ.toAlgebra
  letI i₂ : Algebra S T' := (χ.comp ρ).toAlgebra
  let f : T →ₐ[S] T' := ⟨χ, fun _ => rfl⟩
  exact hn T T' f E' A' gE hgE gA hgA q.φ q.φ' q.hφ q.hp E'' A'' hE hhE hA hhA hgE'' hgA''
    q''.φ q''.φ' q''.hφ q''.hp h1 h2

theorem X3R (hs : SurjZ pt) {T : Type} [CommRing T] (ρ : S →+* T)
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia ρ E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia ρ A A' gA)
    (z : Spec (CommRingCat.of T) ⟶ Z) (hz : z ≫ ζ = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ q : Pair r d E' A', ptP pt ρ E' A' gE hgE gA hgA q = z := by
  letI : Algebra S T := ρ.toAlgebra
  obtain ⟨φ, φ', hφ, hp, h⟩ := hs T E' A' gE hgE gA hgA ⟨z, hz⟩
  exact ⟨⟨φ, φ', hφ, hp⟩, congrArg Subtype.val h⟩

theorem X4R (hi : InjZ pt) {T : Type} [CommRing T] (ρ : S →+* T)
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia ρ E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia ρ A A' gA) (q₁ q₂ : Pair r d E' A')
    (h : ptP pt ρ E' A' gE hgE gA hgA q₁ = ptP pt ρ E' A' gE hgE gA hgA q₂) : q₁ = q₂ := by
  letI : Algebra S T := ρ.toAlgebra
  obtain ⟨h1, h2⟩ := hi T E' A' gE hgE gA hgA q₁.φ q₁.φ' q₁.hφ q₁.hp q₂.φ q₂.φ' q₂.hφ q₂.hp (Subtype.ext h)
  exact Pair.ext' q₁ q₂ h1 h2

theorem PL_iff_of_ptP_eq (hn : NatZ pt) (hi : InjZ pt) {T : Type} [CommRing T] (ρ : S →+* T)
    (E₁ A₁ : FakeEllipticCurve Λ N T) (g₁E : E₁.A ⟶ E.A) (h₁E : FakeEllipticCurve.IsPullbackVia ρ E E₁ g₁E)
    (g₁A : A₁.A ⟶ A.A) (h₁A : FakeEllipticCurve.IsPullbackVia ρ A A₁ g₁A) (q₁ : Pair r d E₁ A₁)
    (E₂ A₂ : FakeEllipticCurve Λ N T) (g₂E : E₂.A ⟶ E.A) (h₂E : FakeEllipticCurve.IsPullbackVia ρ E E₂ g₂E)
    (g₂A : A₂.A ⟶ A.A) (h₂A : FakeEllipticCurve.IsPullbackVia ρ A A₂ g₂A) (q₂ : Pair r d E₂ A₂)
    (h : ptP pt ρ E₁ A₁ g₁E h₁E g₁A h₁A q₁ = ptP pt ρ E₂ A₂ g₂E h₂E g₂A h₂A q₂) :
    q₁.PL → q₂.PL := by
  intro hl₁

  obtain ⟨k, hk, hkp⟩ := exists_comparison ρ E E₁ E₂ g₁E h₁E g₂E h₂E
  obtain ⟨kA, hkA, hkAp⟩ := exists_comparison ρ A A₁ A₂ g₁A h₁A g₂A h₂A
  obtain ⟨q₁'', h1, h2⟩ := exists_pullPair₀ (RingHom.id T) E₁ A₁ E₂ A₂ k hkp kA hkAp q₁
  have hcE : FakeEllipticCurve.IsPullbackVia ((RingHom.id T).comp ρ) E E₂ (k ≫ g₁E) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ (RingHom.id T) E E₁ E₂ g₁E k h₁E hkp
  have hcA : FakeEllipticCurve.IsPullbackVia ((RingHom.id T).comp ρ) A A₂ (kA ≫ g₁A) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ (RingHom.id T) A A₁ A₂ g₁A kA h₁A hkAp
  have hpt : ptP pt ((RingHom.id T).comp ρ) E₂ A₂ (k ≫ g₁E) hcE (kA ≫ g₁A) hcA q₁'' =
      ptP pt ρ E₁ A₁ g₁E h₁E g₁A h₁A q₁ := by
    rw [X2R hn ρ (RingHom.id T) E₁ A₁ g₁E h₁E g₁A h₁A q₁ E₂ A₂ k hkp kA hkAp hcE hcA q₁'' h1 h2, specMap_id,
      Category.id_comp]

  have hpt' : ptP pt ρ E₂ A₂ g₂E h₂E g₂A h₂A q₁'' = ptP pt ρ E₂ A₂ g₂E h₂E g₂A h₂A q₂ := by
    rw [← h, ← hpt]
    exact ptP_congr pt (RingHom.id_comp ρ).symm E₂ A₂ hk.symm hkA.symm h₂E h₂A hcE hcA rfl
  have hq : q₁'' = q₂ := X4R hi ρ E₂ A₂ g₂E h₂E g₂A h₂A q₁'' q₂ hpt'
  subst hq
  intro T₀ t P hP
  exact PL_pull (RingHom.id T) E₁ A₁ E₂ A₂ k hkp kA hkAp q₁ q₁'' h1 hl₁ t P hP

def Q (pt : PtZ r d S E A Z ζ) (B : Type) [CommRing B] (u : Spec (CommRingCat.of B) ⟶ Z) : Prop :=
  ∃ (ρ : S →+* B) (E' A' : FakeEllipticCurve Λ N B) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia ρ E E' gE)
    (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia ρ A A' gA) (q : Pair r d E' A'),
    ptP pt ρ E' A' gE hgE gA hgA q = u ∧ q.PL

theorem hQmap (hn : NatZ pt) : ∀ (B B' : Type) [CommRing B] [CommRing B'] (φ : B →+* B') (u : Spec (CommRingCat.of B) ⟶ Z),
    Q pt B u → Q pt B' (Spec.map (CommRingCat.ofHom φ) ≫ u) := by
  intro B B' _ _ φ u hQ
  obtain ⟨ρ, E', A', gE, hgE, gA, hgA, q, hq, hl⟩ := hQ
  obtain ⟨E'', hE, hhE⟩ := exists_presentation φ E'
  obtain ⟨A'', hA, hhA⟩ := exists_presentation φ A'
  obtain ⟨ψ, ψ', hψ, hq'', hl'', h1, h2⟩ :=
    exists_pullPair φ (r ^ d) E' A' E'' A'' hE hhE hA hhA q.φ q.φ' q.hφ q.hp hl
  have hgE'' : FakeEllipticCurve.IsPullbackVia (φ.comp ρ) E E'' (hE ≫ gE) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ φ E E' E'' gE hE hgE hhE
  have hgA'' : FakeEllipticCurve.IsPullbackVia (φ.comp ρ) A A'' (hA ≫ gA) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ φ A A' A'' gA hA hgA hhA
  refine ⟨φ.comp ρ, E'', A'', hE ≫ gE, hgE'', hA ≫ gA, hgA'', ⟨ψ, ψ', hψ, hq''⟩, ?_, hl''⟩
  rw [X2R hn ρ φ E' A' gE hgE gA hgA q E'' A'' hE hhE hA hhA hgE'' hgA'' ⟨ψ, ψ', hψ, hq''⟩ h1 h2, hq]

theorem hQloc (hn : NatZ pt) (hs : SurjZ pt) (hi : InjZ pt) :
    ∀ (B : Type) [CommRing B] (u : Spec (CommRingCat.of B) ⟶ Z) (ι : Type) (rr : ι → B),
      Ideal.span (Set.range rr) = ⊤ →
      (∀ i, Q pt (Localization.Away (rr i))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (rr i)))) ≫ u)) → Q pt B u := by
  intro B _ u ι rr hrr hloc

  obtain ⟨ρ, hρ⟩ := exists_eq_specMap (u ≫ ζ)
  obtain ⟨E', gE, hgE⟩ := exists_presentation ρ E
  obtain ⟨A', gA, hgA⟩ := exists_presentation ρ A
  obtain ⟨q, hq⟩ := X3R hs ρ E' A' gE hgE gA hgA u hρ.symm
  refine ⟨ρ, E', A', gE, hgE, gA, hgA, q, hq, ?_⟩

  obtain ⟨J, -, hJ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia
      B E' A' q.φ q.hφ
  have hJi : ∀ i, J.map (algebraMap B (Localization.Away (rr i))) = ⊥ := by
    intro i
    obtain ⟨ρi, Ei, Ai, gEi, hgEi, gAi, hgAi, qi, hqi, hli⟩ := hloc i

    obtain ⟨E'', hE, hhE⟩ := exists_presentation (algebraMap B (Localization.Away (rr i))) E'
    obtain ⟨A'', hA, hhA⟩ := exists_presentation (algebraMap B (Localization.Away (rr i))) A'
    obtain ⟨q'', h1, h2⟩ := exists_pullPair₀ (algebraMap B (Localization.Away (rr i))) E' A' E'' A'' hE hhE hA hhA q
    have hgE'' : FakeEllipticCurve.IsPullbackVia ((algebraMap B (Localization.Away (rr i))).comp ρ) E E'' (hE ≫ gE) :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ _ E E' E'' gE hE hgE hhE
    have hgA'' : FakeEllipticCurve.IsPullbackVia ((algebraMap B (Localization.Away (rr i))).comp ρ) A A'' (hA ≫ gA) :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ _ A A' A'' gA hA hgA hhA
    have hpt'' : ptP pt ((algebraMap B (Localization.Away (rr i))).comp ρ) E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' q'' =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (rr i)))) ≫ u := by
      rw [X2R hn ρ _ E' A' gE hgE gA hgA q E'' A'' hE hhE hA hhA hgE'' hgA'' q'' h1 h2, hq]

    have hρi : ρi = (algebraMap B (Localization.Away (rr i))).comp ρ := by
      apply ringHom_eq_of_specMap_eq
      rw [← ptP_over pt ρi Ei Ai gEi hgEi gAi hgAi qi, hqi, specMap_comp ρ (algebraMap B (Localization.Away (rr i))),
        hρ, Category.assoc]
    subst hρi
    have hl'' : q''.PL :=
      PL_iff_of_ptP_eq hn hi _ Ei Ai gEi hgEi gAi hgAi qi E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' q''
        (by rw [hqi, hpt'']) hli
    exact (hJ _ (algebraMap B (Localization.Away (rr i))) E'' A'' hE hhE hA hhA q''.φ q''.hφ h1).mp hl''
  have hJ0 : J = ⊥ := ideal_eq_bot_of_forall_map_away_eq_bot J rr hrr hJi
  have hPL : FakeEllipticCurve.PreservesLevel E' A' q.φ q.hφ :=
    (hJ B (RingHom.id B) E' A' (𝟙 _) (isPullbackVia_id E') (𝟙 _) (isPullbackVia_id A') q.φ q.hφ (by simp)).mpr
      (by rw [hJ0, Ideal.map_bot])
  intro T₀ t P hP
  exact hPL t P hP

theorem hQcut (hn : NatZ pt) (hs : SurjZ pt) (hi : InjZ pt) :
    ∀ (U : Z.Opens) (hU : IsAffineOpen U) (B : Type) [CommRing B]
      (e : Spec (CommRingCat.of B) ≅ (U : Scheme.{0})),
      ∃ J : Ideal B, J.FG ∧ ∀ (B' : Type) [CommRing B'] (φ : B →+* B'),
        Q pt B' (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ↔ Ideal.map φ J = ⊥ := by
  intro U hU B _ e

  obtain ⟨ρ, hρ⟩ := exists_eq_specMap ((e.hom ≫ U.ι) ≫ ζ)
  obtain ⟨E', gE, hgE⟩ := exists_presentation ρ E
  obtain ⟨A', gA, hgA⟩ := exists_presentation ρ A
  obtain ⟨q₀, hq₀⟩ := X3R hs ρ E' A' gE hgE gA hgA (e.hom ≫ U.ι) hρ.symm

  obtain ⟨J, hJfg, hJ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia
      B E' A' q₀.φ q₀.hφ
  refine ⟨J, hJfg, fun B' _ φ => ?_⟩

  obtain ⟨E'', hE, hhE⟩ := exists_presentation φ E'
  obtain ⟨A'', hA, hhA⟩ := exists_presentation φ A'
  obtain ⟨q'', h1, h2⟩ := exists_pullPair₀ φ E' A' E'' A'' hE hhE hA hhA q₀
  have hgE'' : FakeEllipticCurve.IsPullbackVia (φ.comp ρ) E E'' (hE ≫ gE) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ φ E E' E'' gE hE hgE hhE
  have hgA'' : FakeEllipticCurve.IsPullbackVia (φ.comp ρ) A A'' (hA ≫ gA) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ρ φ A A' A'' gA hA hgA hhA
  have hpt'' : ptP pt (φ.comp ρ) E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' q'' =
      Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι := by
    rw [X2R hn ρ φ E' A' gE hgE gA hgA q₀ E'' A'' hE hhE hA hhA hgE'' hgA'' q'' h1 h2, hq₀]
  have key : q''.PL ↔ Ideal.map φ J = ⊥ := hJ B' φ E'' A'' hE hhE hA hhA q''.φ q''.hφ h1
  constructor
  · rintro ⟨ρ', E₁, A₁, g₁E, h₁E, g₁A, h₁A, q₁, hq₁, hl₁⟩
    have hρ' : ρ' = φ.comp ρ := by
      apply ringHom_eq_of_specMap_eq
      rw [← ptP_over pt ρ' E₁ A₁ g₁E h₁E g₁A h₁A q₁, hq₁, specMap_comp ρ φ, hρ, Category.assoc, Category.assoc]
    subst hρ'
    exact key.mp (PL_iff_of_ptP_eq hn hi _ E₁ A₁ g₁E h₁E g₁A h₁A q₁ E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' q''
      (by rw [hq₁, hpt'']) hl₁)
  · intro hJ0
    exact ⟨φ.comp ρ, E'', A'', hE ≫ gE, hgE'', hA ≫ gA, hgA'', q'', hpt'', key.mpr hJ0⟩

theorem main (hn : NatZ pt) (hs : SurjZ pt) (hi : InjZ pt) :
    ∃ (Y : Scheme.{0}) (ι : Y ⟶ Z), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ'),
        FakeEllipticCurve.PreservesLevel E' A' φ hφ ↔
          ∃ y : Spec (CommRingCat.of T) ⟶ Y, y ≫ ι = (pt T E' A' gE hgE gA hgA φ φ' hφ hp).1 := by
  obtain ⟨Y, ι, hcl, hlfp, hY⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut Z (Q pt)
      (hQmap hn) (hQloc hn hs hi) (hQcut hn hs hi)
  refine ⟨Y, ι, hcl, hlfp, fun T _ _ E' A' gE hgE gA hgA φ φ' hφ hp => ?_⟩
  rw [hY]
  constructor
  · intro hl
    exact ⟨algebraMap S T, E', A', gE, hgE, gA, hgA, ⟨φ, φ', hφ, hp⟩,
      (pt_eq_ptP pt (algebraMap S T) rfl E' A' gE hgE gA hgA φ φ' hφ hp hgE hgA).symm, hl⟩
  · rintro ⟨ρ, E₁, A₁, g₁E, h₁E, g₁A, h₁A, q₁, hq₁, hl₁⟩

    have hρ : ρ = algebraMap S T := by
      apply ringHom_eq_of_specMap_eq
      rw [← ptP_over pt ρ E₁ A₁ g₁E h₁E g₁A h₁A q₁, hq₁]
      exact (pt T E' A' gE hgE gA hgA φ φ' hφ hp).2
    subst hρ
    rw [pt_eq_ptP pt (algebraMap S T) rfl E' A' gE hgE gA hgA φ φ' hφ hp hgE hgA] at hq₁
    have h2 : (⟨φ, φ', hφ, hp⟩ : Pair r d E' A').PL :=
      PL_iff_of_ptP_eq hn hi (algebraMap S T) E₁ A₁ g₁E h₁E g₁A h₁A q₁ E' A' gE hgE gA hgA ⟨φ, φ', hφ, hp⟩ hq₁ hl₁
    intro T₀ t P hP
    exact @h2 T₀ t P hP

end Contract

end P3bS14

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S))
    (ptZ : ∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
        FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ)
    (hZ1 : (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
          (gA'' : A''.A ⟶ A.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
          (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
          FakeEllipticCurve.IsoVia E' E'' iE hiE → FakeEllipticCurve.IsoVia A' A'' iA hiA →
          iE.hom ≫ gE'' = gE → iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom → iA.hom ≫ ψ' = φ' ≫ iE.hom →
            ptZ T E' A' gE hgE gA hgA φ φ' hφ hp = ptZ T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq))
    (hZ2 : (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
          (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
          (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
          (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ'),
          ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
            (ptZ T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq).1 =
              Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (ptZ T E' A' gE hgE gA hgA φ φ' hφ hp).1))
    (hZ3 : (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ζ),
          ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
            (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ'),
            ptZ T E' A' gE hgE gA hgA φ φ' hφ hp = z))
    (hZ4 : (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
          (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
          (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
          (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂'),
          ptZ T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ = ptZ T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ → φ₁ = φ₂ ∧ φ₁' = φ₂')) :
    ∃ (Y : Scheme.{0}) (ι : Y ⟶ Z), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ'),
          FakeEllipticCurve.PreservesLevel E' A' φ hφ ↔
            ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) (ι ≫ ζ),
              y.1 ≫ ι = (ptZ T E' A' gE hgE gA hgA φ φ' hφ hp).1 := by
  obtain ⟨Y, ι, hcl, hlfp, hY⟩ := P3bS14.main (pt := ptZ) hZ2 hZ3 hZ4
  refine ⟨Y, ι, hcl, hlfp, fun T _ _ E' A' gE hgE gA hgA φ φ' hφ hp => ?_⟩
  rw [hY T E' A' gE hgE gA hgA φ φ' hφ hp]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨⟨y, ?_⟩, hy⟩
    rw [← Category.assoc, hy]
    exact (ptZ T E' A' gE hgE gA hgA φ φ' hφ hp).2
  · rintro ⟨y, hy⟩
    exact ⟨y.1, hy⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_locallyOfFinitePresentation_preservesLevel_iff_of_represents_isIsogenyPair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_locallyOfFinitePresentation_preservesLevel_iff_of_represents_isIsogenyPair (solution)
