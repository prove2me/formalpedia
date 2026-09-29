-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fullLevel_eq_of_forall_isPullbackVia_isLocalizationAway_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7925b097-b744-5616-a487-aca74201ebaa

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_eq_of_forall_isPullbackVia_isLocalizationAway_of_span_eq_top

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

namespace P2mS14FullLevelLocal

universe u

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem comp_nsmulPt {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (k : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t k x) = nsmulPt L t' k (schemeHomOverComp ψ hψ x) := by
  induction k with
  | zero => exact L.one_natural t t' ψ hψ
  | succ k ih => simp only [nsmulPt]; rw [L.mul_natural, ih]

variable {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}

theorem one_comp_eq (hg : FakeEllipticCurve.IsPullbackVia φ E E' g)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (u : T ⟶ Spec (CommRingCat.of S))
    (hu : t' ≫ Spec.map (CommRingCat.ofHom φ) = u) :
    (E'.L.one t').1 ≫ g = (E.L.one u).1 := by
  subst hu
  obtain ⟨hpb, hmul, -, -⟩ := hg
  let o : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
    ⟨(E'.L.one t').1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, (E'.L.one t').2]⟩
  have h2 : E.L.mul _ o o = o := by
    apply Subtype.ext
    have := hmul t' (E'.L.one t') (E'.L.one t')
    rw [E'.L.mul_one] at this
    exact this.symm
  letI := E.L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h3 : o = 1 := (mul_eq_left (a := o) (b := o)).mp h2
  change o.1 = (E.L.one _).1
  rw [h3]
  rfl

theorem nsmulPt_comp_eq (hg : FakeEllipticCurve.IsPullbackVia φ E E' g)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (u : T ⟶ Spec (CommRingCat.of S))
    (hu : t' ≫ Spec.map (CommRingCat.ofHom φ) = u) (k : ℕ) (Q : SchemeHomOver t' E'.f)
    (hQ : (Q.1 ≫ g) ≫ E.f = u) :
    (nsmulPt E'.L t' k Q).1 ≫ g = (nsmulPt E.L u k ⟨Q.1 ≫ g, hQ⟩).1 := by
  subst hu
  have hg' := hg
  obtain ⟨hpb, hmul, -, -⟩ := hg
  induction k with
  | zero =>
    simp only [nsmulPt]
    exact one_comp_eq hg' t' _ rfl
  | succ k ih =>
    simp only [nsmulPt]
    rw [hmul]
    congr 2
    exact Subtype.ext ih

end P2mS14FullLevelLocal

open P2mS14FullLevelLocal in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℕ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (n : ℕ) (c : Fin n → S) (hc : Ideal.span (Set.range c) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra S (L i)] [∀ i, IsLocalization.Away (c i) (L i)]
    (Ei : ∀ i, FakeEllipticCurve Λ N (L i)) (g : ∀ i, (Ei i).A ⟶ E.A)
    (hg : ∀ i, FakeEllipticCurve.IsPullbackVia (algebraMap S (L i)) E (Ei i) (g i))
    (Pi : ∀ i, (Ei i).FullLevel m)
    (hPi : ∀ i, ((Pi i).P).1 ≫ g i = Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ P.1) :
    ∃ Pm : E.FullLevel m, Pm.P = P := by
  classical

  set s : ∀ i, Spec (CommRingCat.of (L i)) ⟶ Spec (CommRingCat.of S) :=
    fun i => Spec.map (CommRingCat.ofHom (algebraMap S (L i))) with hs

  let 𝒰 : (Spec (CommRingCat.of S)).OpenCover :=
    { I₀ := Fin n
      X := fun i => Spec (CommRingCat.of (L i))
      f := fun i => Spec.map (CommRingCat.ofHom (algebraMap S (L i)))
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, fun i => IsOpenImmersion.of_isLocalization (c i)⟩
        have hx : ∃ i, c i ∉ x.asIdeal := by
          by_contra! h
          apply x.2.ne_top
          rwa [← top_le_iff, ← hc, Ideal.span_le, Set.range_subset_iff]
        obtain ⟨i, hi⟩ := hx
        refine ⟨i, ?_⟩
        have := PrimeSpectrum.localization_away_comap_range (L i) (c i)
        exact (eq_iff_iff.mp congr(x ∈ $this)).mpr hi }
  refine ⟨⟨P, ?_, ?_, ?_⟩, rfl⟩
  ·
    apply Subtype.ext
    apply 𝒰.hom_ext
    intro i
    obtain ⟨hpb, hmul, hact, hlev⟩ := hg i
    change s i ≫ (nsmulPt E.L (𝟙 _) m P).1 = s i ≫ (E.L.one (𝟙 _)).1
    have e1 := congrArg Subtype.val (comp_nsmulPt E.L (𝟙 _) (s i) (s i) (Category.comp_id _) m P)
    have e2 := congrArg Subtype.val (E.L.one_natural (𝟙 _) (s i) (s i) (Category.comp_id _))
    simp only [schemeHomOverComp_coe] at e1 e2
    rw [e1, e2]
    have hP' : (((Pi i).P).1 ≫ g i) ≫ E.f = s i := by
      rw [hPi, Category.assoc, P.2, Category.comp_id]
    have e3 := nsmulPt_comp_eq (hg i) (𝟙 _) (s i) (Category.id_comp _) m (Pi i).P hP'
    rw [(Pi i).torsion] at e3
    have e4 := one_comp_eq (hg i) (𝟙 _) (s i) (Category.id_comp _)
    have hq : (⟨((Pi i).P).1 ≫ g i, hP'⟩ : SchemeHomOver (s i) E.f) = schemeHomOverComp (s i) (Category.comp_id _) P :=
      Subtype.ext (by rw [schemeHomOverComp_coe]; exact hPi i)
    rw [← hq, ← e3, e4]
  ·
    intro k _ _ sk Q hQ

    have hunit : ∃ i, IsUnit (sk (c i)) := by
      by_contra! h
      have hz : ∀ i, sk (c i) = 0 := fun i => by simpa [isUnit_iff_ne_zero] using h i
      have h1 : (1 : S) ∈ Ideal.span (Set.range c) := by rw [hc]; exact Submodule.mem_top
      obtain ⟨coef, hcoef⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
      have h2 := congrArg sk hcoef
      rw [map_sum, map_one] at h2
      refine one_ne_zero (h2.symm.trans ?_)
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hz i, mul_zero]
    obtain ⟨i, hi⟩ := hunit
    obtain ⟨ski, hski⟩ : ∃ ski : L i →+* k, ski.comp (algebraMap S (L i)) = sk :=
      ⟨IsLocalization.Away.lift (c i) hi, IsLocalization.Away.lift_comp (c i) hi⟩
    subst hski
    obtain ⟨hpb, hmul, hact, hlev⟩ := hg i
    have hgeo : geomPoint k ski ≫ s i = geomPoint k (ski.comp (algebraMap S (L i))) := by
      simp only [hs, geomPoint]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

    let Qi : SchemeHomOver (geomPoint k ski) (Ei i).f :=
      ⟨hpb.lift Q.1 (geomPoint k ski) (by rw [Q.2, ← hgeo]), hpb.lift_snd _ _ _⟩
    have hQi1 : Qi.1 ≫ g i = Q.1 := hpb.lift_fst _ _ _
    have hQu : (Qi.1 ≫ g i) ≫ E.f = geomPoint k (ski.comp (algebraMap S (L i))) := by rw [hQi1, Q.2]
    have e := nsmulPt_comp_eq (hg i) (geomPoint k ski) _ hgeo m Qi hQu
    have hQQ : (⟨Qi.1 ≫ g i, hQu⟩ : SchemeHomOver (geomPoint k (ski.comp (algebraMap S (L i)))) E.f) = Q :=
      Subtype.ext hQi1
    rw [hQQ, hQ] at e
    have e1 := one_comp_eq (hg i) (geomPoint k ski) _ hgeo
    have htQi : nsmulPt (Ei i).L (geomPoint k ski) m Qi = (Ei i).L.one _ := by
      apply Subtype.ext
      apply hpb.hom_ext
      · rw [e, e1]
      · rw [(nsmulPt _ _ m Qi).2, ((Ei i).L.one _).2]
    obtain ⟨x, hx⟩ := (Pi i).generates k ski Qi htQi
    refine ⟨x, Subtype.ext ?_⟩
    have h3 := congrArg (fun R : SchemeHomOver (geomPoint k ski) (Ei i).f => R.1 ≫ g i) hx
    simp only [FakeEllipticCurve.sectionAt, mapPt_coe, schemeHomOverComp_coe, Category.assoc] at h3 ⊢
    rw [hact x, reassoc_of% (hPi i), hQi1] at h3
    simp only [hs] at hgeo
    rw [reassoc_of% hgeo] at h3
    exact h3
  ·
    intro k _ _ sk x
    have hunit : ∃ i, IsUnit (sk (c i)) := by
      by_contra! h
      have hz : ∀ i, sk (c i) = 0 := fun i => by simpa [isUnit_iff_ne_zero] using h i
      have h1 : (1 : S) ∈ Ideal.span (Set.range c) := by rw [hc]; exact Submodule.mem_top
      obtain ⟨coef, hcoef⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
      have h2 := congrArg sk hcoef
      rw [map_sum, map_one] at h2
      refine one_ne_zero (h2.symm.trans ?_)
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hz i, mul_zero]
    obtain ⟨i, hi⟩ := hunit
    obtain ⟨ski, hski⟩ : ∃ ski : L i →+* k, ski.comp (algebraMap S (L i)) = sk :=
      ⟨IsLocalization.Away.lift (c i) hi, IsLocalization.Away.lift_comp (c i) hi⟩
    subst hski
    obtain ⟨hpb, hmul, hact, hlev⟩ := hg i
    have hgeo : geomPoint k ski ≫ s i = geomPoint k (ski.comp (algebraMap S (L i))) := by
      simp only [hs, geomPoint]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e1 := one_comp_eq (hg i) (geomPoint k ski) _ hgeo
    have hR : (pushPt ((Ei i).act x) ((Ei i).act_over x) (FakeEllipticCurve.sectionAt (Pi i).P k ski)).1 ≫ g i =
        (pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k (ski.comp (algebraMap S (L i))))).1 := by
      simp only [FakeEllipticCurve.sectionAt, mapPt_coe, schemeHomOverComp_coe, Category.assoc]
      rw [hact x, reassoc_of% (hPi i), ← hgeo, Category.assoc]
    rw [← (Pi i).annihilator k ski x]
    constructor
    · intro H
      apply Subtype.ext
      apply hpb.hom_ext
      · rw [hR, e1]; exact congrArg Subtype.val H
      · rw [(pushPt _ _ _).2, ((Ei i).L.one _).2]
    · intro H
      apply Subtype.ext
      rw [← hR, H, e1]

#print axioms solution

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_eq_of_forall_isPullbackVia_isLocalizationAway_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_eq_of_forall_isPullbackVia_isLocalizationAway_of_span_eq_top (solution)
