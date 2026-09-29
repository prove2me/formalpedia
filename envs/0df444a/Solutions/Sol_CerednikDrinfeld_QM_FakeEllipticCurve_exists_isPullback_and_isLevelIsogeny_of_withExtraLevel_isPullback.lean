-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_and_isLevelIsogeny_of_withExtraLevel_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/aaad571e-d767-5ee3-8fa7-993c4f498c0d

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_levK_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_and_isLevelIsogeny_of_withExtraLevel_isPullback
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open CerednikDrinfeld.QM.FakeEllipticCurve

namespace BaseChange21

variable {R : Type} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  letI := L.pointGroup t
  have h2 : y * y = y * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel h2

end BaseChange21

open BaseChange21 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (ℓ : ℕ)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (huu' : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u')
    (d : FakeEllipticCurve Λ N S) (hud : FakeEllipticCurve.IsLevelIsogeny ℓ u d) :
    ∃ d' : FakeEllipticCurve Λ N S', FakeEllipticCurve.IsPullback φ d d' ∧ FakeEllipticCurve.IsLevelIsogeny ℓ u' d' := by
  classical
  obtain ⟨g, hg, g_mul, g_act, g_lev⟩ := huu'
  obtain ⟨φd, hφd, ψd, hψd, mφd, mψd, aφd, aψd, cd, kd, ld⟩ := hud
  obtain ⟨d', gd, hgd, gd_mul, gd_act, gd_lev, gd_lev'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff φ d
  set σ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom φ) with hσ

  have wφ : (g ≫ φd) ≫ d.f = u'.1.f ≫ σ := by rw [Category.assoc, hφd]; exact hg.w
  let φ' : u'.1.A ⟶ d'.A := hgd.lift (g ≫ φd) u'.1.f wφ
  have hφ'g : φ' ≫ gd = g ≫ φd := hgd.lift_fst _ _ _
  have hφ' : φ' ≫ d'.f = u'.1.f := hgd.lift_snd _ _ _
  have wψ : (gd ≫ ψd) ≫ u.1.f = d'.f ≫ σ := by rw [Category.assoc, hψd]; exact hgd.w
  let ψ' : d'.A ⟶ u'.1.A := hg.lift (gd ≫ ψd) d'.f wψ
  have hψ'g : ψ' ≫ g = gd ≫ ψd := hg.lift_fst _ _ _
  have hψ' : ψ' ≫ u'.1.f = d'.f := hg.lift_snd _ _ _

  let pg : ∀ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')}, SchemeHomOver t' u'.1.f → SchemeHomOver (t' ≫ σ) u.1.f :=
    fun {T} {t'} P => ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
  let pd : ∀ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')}, SchemeHomOver t' d'.f → SchemeHomOver (t' ≫ σ) d.f :=
    fun {T} {t'} Q => ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩
  have pg_inj : ∀ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P P' : SchemeHomOver t' u'.1.f),
      pg P = pg P' → P = P' := by
    intro T t' P P' h
    apply Subtype.ext
    exact hg.hom_ext (congrArg Subtype.val h) (by rw [P.2, P'.2])
  have pd_inj : ∀ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (Q Q' : SchemeHomOver t' d'.f),
      pd Q = pd Q' → Q = Q' := by
    intro T t' Q Q' h
    apply Subtype.ext
    exact hgd.hom_ext (congrArg Subtype.val h) (by rw [Q.2, Q'.2])
  have pg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' u'.1.f),
      pg (u'.1.L.mul t' P Q) = u.1.L.mul _ (pg P) (pg Q) := fun t' P Q => Subtype.ext (g_mul t' P Q)
  have pd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' d'.f),
      pd (d'.L.mul t' P Q) = d.L.mul _ (pd P) (pd Q) := fun t' P Q => Subtype.ext (gd_mul t' P Q)
  have pg_one : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')), pg (u'.1.L.one t') = u.1.L.one _ := by
    intro T t'
    apply eq_one_of_mul_self
    rw [← pg_mul, u'.1.L.one_mul]
  have pd_one : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')), pd (d'.L.one t') = d.L.one _ := by
    intro T t'
    apply eq_one_of_mul_self
    rw [← pd_mul, d'.L.one_mul]
  have pd_φ' : ∀ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' u'.1.f),
      pd (mapPt φ' hφ' P) = mapPt φd hφd (pg P) := by
    intro T t' P
    apply Subtype.ext
    show (P.1 ≫ φ') ≫ gd = (P.1 ≫ g) ≫ φd
    rw [Category.assoc, hφ'g, Category.assoc]
  have pg_ψ' : ∀ {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (Q : SchemeHomOver t' d'.f),
      pg (mapPt ψ' hψ' Q) = mapPt ψd hψd (pd Q) := by
    intro T t' Q
    apply Subtype.ext
    show (Q.1 ≫ ψ') ≫ g = (Q.1 ≫ gd) ≫ ψd
    rw [Category.assoc, hψ'g, Category.assoc]
  refine ⟨d', ⟨gd, hgd, gd_mul, gd_act, fun t' P h => gd_lev t' P h⟩, φ', hφ', ψ', hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t' P Q
    apply pd_inj
    rw [pd_φ', pg_mul, mφd, pd_mul, pd_φ', pd_φ']
  ·
    intro T t' P Q
    apply pg_inj
    rw [pg_ψ', pd_mul, mψd, pg_mul, pg_ψ', pg_ψ']
  ·
    intro x
    apply hgd.hom_ext
    · show (u'.1.act x ≫ φ') ≫ gd = (φ' ≫ d'.act x) ≫ gd
      rw [Category.assoc, hφ'g, ← Category.assoc, g_act x, Category.assoc, aφd x, Category.assoc, gd_act x,
        ← Category.assoc φ' gd (d.act x), hφ'g, Category.assoc]
    · show (u'.1.act x ≫ φ') ≫ d'.f = (φ' ≫ d'.act x) ≫ d'.f
      rw [Category.assoc, hφ', u'.1.act_over, Category.assoc, d'.act_over, hφ']
  ·
    intro x
    apply hg.hom_ext
    · show (d'.act x ≫ ψ') ≫ g = (ψ' ≫ u'.1.act x) ≫ g
      rw [Category.assoc, hψ'g, ← Category.assoc, gd_act x, Category.assoc, aψd x, Category.assoc, g_act x,
        ← Category.assoc ψ' g (u.1.act x), hψ'g, Category.assoc]
    · show (d'.act x ≫ ψ') ≫ u'.1.f = (ψ' ≫ u'.1.act x) ≫ u'.1.f
      rw [Category.assoc, hψ', d'.act_over, Category.assoc, u'.1.act_over, hψ']
  ·
    intro hℓ
    obtain ⟨c1, c2⟩ := cd hℓ
    constructor
    · apply hg.hom_ext
      · show (φ' ≫ ψ') ≫ g = u'.1.act _ ≫ g
        rw [Category.assoc, hψ'g, ← Category.assoc, hφ'g, Category.assoc, c1, g_act]
      · show (φ' ≫ ψ') ≫ u'.1.f = u'.1.act _ ≫ u'.1.f
        rw [Category.assoc, hψ', hφ', u'.1.act_over]
    · apply hgd.hom_ext
      · show (ψ' ≫ φ') ≫ gd = d'.act _ ≫ gd
        rw [Category.assoc, hφ'g, ← Category.assoc, hψ'g, Category.assoc, c2, gd_act]
      · show (ψ' ≫ φ') ≫ d'.f = d'.act _ ≫ d'.f
        rw [Category.assoc, hφ', hψ', d'.act_over]
  ·
    intro T t' P
    constructor
    · intro hP
      have h1 : mapPt φd hφd (pg P) = d.L.one _ := by rw [← pd_φ', hP, pd_one]
      have h2 : FactorsThrough u.2.levK (pg P) := (kd _ _).1 h1
      obtain ⟨P₀, hP₀⟩ := h2
      exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_levK_of_exists_comp_eq_of_isPullback φ u u' g hg
        (fun t' P h => (g_lev t' P).2 h) t' P ⟨P₀, hP₀⟩
    · intro hP
      obtain ⟨P₀, hP₀⟩ := (g_lev t' P).2 hP
      have h2 : FactorsThrough u.2.levK (pg P) := ⟨P₀, hP₀⟩
      have h1 : mapPt φd hφd (pg P) = d.L.one _ := (kd _ _).2 h2
      apply pd_inj
      rw [pd_φ', h1, pd_one]
  ·
    intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := (g_lev t' P).1 hP
    have h1 : FactorsThrough u.1.lev (pg P) := ⟨P₀, hP₀⟩
    have h2 : FactorsThrough d.lev (mapPt φd hφd (pg P)) := ld _ _ h1
    rw [← pd_φ'] at h2
    obtain ⟨Q₀, hQ₀⟩ := h2
    exact gd_lev' t' (mapPt φ' hφ' P) ⟨Q₀, hQ₀⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_and_isLevelIsogeny_of_withExtraLevel_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_and_isLevelIsogeny_of_withExtraLevel_isPullback (solution)
