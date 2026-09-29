-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/32dfdebd-8c5c-5a19-971e-dc311db7cae0

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

set_option maxHeartbeats 3200000

namespace C1u6
p2m_open "CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM.FakeEllipticCurve"

theorem mapPt_mapPt {R : Type} [CommRing R] {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) (hφψ : (φ ≫ ψ) ≫ f'' = f) :
    mapPt (φ ≫ ψ) hφψ P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp only [mapPt_coe, Category.assoc]

theorem reduceAL {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (r : ℕ) [Fact r.Prime] (hrN : ¬ r ∣ N)
    {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S')
    (E E' : FakeEllipticCurve Λ N S) (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (hAL : IsAtkinLehnerQuotientVia r E E' q hq q' hq')
    (Eb : FakeEllipticCurve Λ N S') (gb : Eb.A ⟶ E.A) (hEb : IsPullbackVia f E Eb gb)
    (Eb' : FakeEllipticCurve Λ N S') (gb' : Eb'.A ⟶ E'.A) (hEb' : IsPullbackVia f E' Eb' gb') :
    ∃ (qb : Eb.A ⟶ Eb'.A) (hqb : qb ≫ Eb'.f = Eb.f) (qb' : Eb'.A ⟶ Eb.A) (hqb' : qb' ≫ Eb.f = Eb'.f),
      qb ≫ gb' = gb ≫ q ∧ qb' ≫ gb = gb' ≫ q' ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t Eb.f),
        mapPt qb hqb (Eb.L.mul t P Q) = Eb'.L.mul t (mapPt qb hqb P) (mapPt qb hqb Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t Eb'.f),
        mapPt qb' hqb' (Eb'.L.mul t P Q) = Eb.L.mul t (mapPt qb' hqb' P) (mapPt qb' hqb' Q)) ∧
      (∀ x : ↥Λ, Eb.act x ≫ qb = qb ≫ Eb'.act x) ∧ (∀ x : ↥Λ, Eb'.act x ≫ qb' = qb' ≫ Eb.act x) ∧
      (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
        qb ≫ qb' = Eb.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧ qb' ≫ qb = Eb'.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
      PreservesLevel Eb' Eb qb' hqb' := by
  classical
  obtain ⟨q_hom, q'_hom, q_act, q'_act, hcomp, hker, q_lev⟩ := hAL
  obtain ⟨hg, hmulE, hactE, hlevE⟩ := hEb
  obtain ⟨hg', hmulE', hactE', hlevE'⟩ := hEb'
  have q'_lev : PreservesLevel E' E q' hq' :=
    CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd hΛℤ r hrN E E' q hq q' hq'
      ⟨q_hom, q'_hom, q_act, q'_act, hcomp, hker, q_lev⟩
  set sf := Spec.map (CommRingCat.ofHom f) with hsf

  have w1 : (gb ≫ q) ≫ E'.f = Eb.f ≫ sf := by rw [Category.assoc, hq, hg.w]
  have w2 : (gb' ≫ q') ≫ E.f = Eb'.f ≫ sf := by rw [Category.assoc, hq', hg'.w]
  let qb : Eb.A ⟶ Eb'.A := hg'.lift (gb ≫ q) Eb.f w1
  let qb' : Eb'.A ⟶ Eb.A := hg.lift (gb' ≫ q') Eb'.f w2
  have hqg : qb ≫ gb' = gb ≫ q := hg'.lift_fst _ _ _
  have hqb : qb ≫ Eb'.f = Eb.f := hg'.lift_snd _ _ _
  have hqg' : qb' ≫ gb = gb' ≫ q' := hg.lift_fst _ _ _
  have hqb' : qb' ≫ Eb.f = Eb'.f := hg.lift_snd _ _ _

  let G : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')), SchemeHomOver t Eb.f → SchemeHomOver (t ≫ sf) E.f :=
    fun t P => ⟨P.1 ≫ gb, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
  let G' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')), SchemeHomOver t Eb'.f → SchemeHomOver (t ≫ sf) E'.f :=
    fun t P => ⟨P.1 ≫ gb', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
  have hG : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t Eb.f),
      G t (Eb.L.mul t P Q) = E.L.mul _ (G t P) (G t Q) := fun t P Q => Subtype.ext (hmulE t P Q)
  have hG' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t Eb'.f),
      G' t (Eb'.L.mul t P Q) = E'.L.mul _ (G' t P) (G' t Q) := fun t P Q => Subtype.ext (hmulE' t P Q)
  have G_inj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t Eb.f), G t P = G t Q → P = Q := by
    intro T t P Q h
    apply Subtype.ext
    exact hg.hom_ext (congrArg Subtype.val h) (by rw [P.2, Q.2])
  have G'_inj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t Eb'.f), G' t P = G' t Q → P = Q := by
    intro T t P Q h
    apply Subtype.ext
    exact hg'.hom_ext (congrArg Subtype.val h) (by rw [P.2, Q.2])
  have hGq : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t Eb.f),
      G' t (mapPt qb hqb P) = mapPt q hq (G t P) := by
    intro T t P; apply Subtype.ext; simp only [G, G', mapPt_coe, Category.assoc, hqg]
  have hGq' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t Eb'.f),
      G t (mapPt qb' hqb' P) = mapPt q' hq' (G' t P) := by
    intro T t P; apply Subtype.ext; simp only [G, G', mapPt_coe, Category.assoc, hqg']
  refine ⟨qb, hqb, qb', hqb', hqg, hqg', ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    apply G'_inj t
    rw [hGq, hG, q_hom, hG', hGq, hGq]
  · intro T t P Q
    apply G_inj t
    rw [hGq', hG', q'_hom, hG, hGq', hGq']
  ·
    intro x
    apply hg'.hom_ext
    · rw [Category.assoc, hqg, Category.assoc, hactE', reassoc_of% hqg, reassoc_of% hactE, q_act]
    · rw [Category.assoc, hqb, Eb.act_over, Category.assoc, Eb'.act_over, hqb]
  · intro x
    apply hg.hom_ext
    · rw [Category.assoc, hqg', Category.assoc, hactE, reassoc_of% hqg', reassoc_of% hactE', q'_act]
    · rw [Category.assoc, hqb', Eb'.act_over, Category.assoc, Eb.act_over, hqb']
  ·
    intro hr
    obtain ⟨hc1, hc2⟩ := hcomp hr
    constructor
    · apply hg.hom_ext
      · rw [Category.assoc, hqg', ← Category.assoc, hqg, Category.assoc, hc1, hactE]
      · rw [Category.assoc, hqb', hqb, Eb.act_over]
    · apply hg'.hom_ext
      · rw [Category.assoc, hqg, ← Category.assoc, hqg', Category.assoc, hc2, hactE']
      · rw [Category.assoc, hqb, hqb', Eb'.act_over]
  ·
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hlevE' t P hP
    have h1 : FactorsThrough E'.lev (G' t P) := ⟨P₀, hP₀⟩
    have h2 := q'_lev _ _ h1
    rw [← hGq'] at h2
    exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia E f Eb gb
      ⟨hg, hmulE, hactE, hlevE⟩ t (mapPt qb' hqb' P) h2

end C1u6

open C1u6 in
theorem solution
    {r N : ℕ} [Fact r.Prime]

    (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (hFV : (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
        mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
        mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q)) ∧
      (∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) ∧ (∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
        FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
        FactorsThrough A₀r.lev Q → FactorsThrough A₀.lev (mapPt V hV Q)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
        mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
        mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q) ∧
      (∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
        x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
      (E E' : FakeEllipticCurve Λ N B)
      (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f),
      FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq' →
      ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
      ∃ ρ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr 1 ψ) E',
        (∃ (qb : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : qb ≫ ρ'.gb = ρ.gb ≫ q) (_ : qb ≫ ρ'.Eb.f = ρ.Eb.f)
          (uA : ρ'.Ab.A ⟶ A₀r.A)
          (_ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρ'.Ab uA)
          (_ : uA ≫ prA = ρ'.gA)
          (Fb : ρ.Ab.A ⟶ ρ'.Ab.A) (_ : Fb ≫ uA = ρ.gA ≫ F) (_ : Fb ≫ ρ'.Ab.f = ρ.Ab.f)
          (i j : ℕ),
          qb ≫ ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ Fb ≫ ρ'.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)  := by
  intro B _ _ ψ E E' q hq q' hq' hAL ρ
  obtain ⟨F_hom, V_hom, F_act, V_act, F_lev, V_lev, V_F, F_V, F_frob⟩ := hFV

  have hσ : ((Fr ^ (1 : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) = (Fr : Onr →ₐ[𝒪] Onr) := by rw [zpow_one]
  have hprA' : FakeEllipticCurve.IsPullbackVia
      (FakeEllipticCurve.Rigidification.residueLeg π ((Fr ^ (1 : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA := by
    rw [hσ]; exact hprA
  obtain ⟨ρp, ub, hub, hubf, gA', hgA', hgA'pr, Fb, hFb, hFbf, Vb, hVb, hVbf, hd, hφp, hφp'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
      𝒪 π Onr ((Fr ^ (1 : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) Λ hΛℤ A₀ A₀r prA hprA' F hF V hV
      F_hom V_hom F_act V_act F_lev V_F F_V B ψ E ρ

  obtain ⟨Eb', gb', hgb', hmul', hact', hlev', hlev'2⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E'
  have hEb' : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E' Eb' gb' :=
    ⟨hgb', hmul', hact', hlev'⟩
  obtain ⟨qb, hqb, qb', hqb', hqg, hqg', qb_hom, qb'_hom, qb_act, qb'_act, hqq, qb'_lev⟩ :=
    reduceAL hΛℤ r hrN (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E E' q hq q' hq' hAL
      ρp.Eb ρp.gb ρp.isPullback_Eb Eb' gb' hEb'

  obtain ⟨hφo, hφ'o, φ_hom, φ'_hom, φ_act, φ'_act, hφφ'⟩ := ρp.isIsogenyPair
  have hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ r
  have hrd : (((r ^ ρp.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ (r ^ ρp.d : ℕ)
  have hrd1 : (((r ^ (ρp.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ (r ^ (ρp.d + 1) : ℕ)
  obtain ⟨h1, h2⟩ := hφφ' hrd
  obtain ⟨hqq1, hqq2⟩ := hqq hr

  have hprod1 : (((r : ℚ) : ℍ[ℚ, a, b])) * (((r ^ ρp.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) = (((r ^ (ρp.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
  have hprod2 : (((r ^ ρp.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) * ((r : ℚ) : ℍ[ℚ, a, b]) = (((r ^ (ρp.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
  have key1 : ∀ (X : FakeEllipticCurve Λ N (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (h : (((r ^ (ρp.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ),
      X.act ⟨_, h⟩ = X.act ⟨_, hrd⟩ ≫ X.act ⟨_, hr⟩ := by
    intro X h
    have hm : ((⟨_, hr⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨_, hrd⟩ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [hprod1]; exact h
    have := X.act_mul ⟨_, hr⟩ ⟨_, hrd⟩ hm
    rw [← this]; congr 1; exact Subtype.ext hprod1.symm
  have key2 : ∀ (X : FakeEllipticCurve Λ N (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (h : (((r ^ (ρp.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ),
      X.act ⟨_, h⟩ = X.act ⟨_, hr⟩ ≫ X.act ⟨_, hrd⟩ := by
    intro X h
    have hm : ((⟨_, hrd⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨_, hr⟩ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [hprod2]; exact h
    have := X.act_mul ⟨_, hrd⟩ ⟨_, hr⟩ hm
    rw [← this]; congr 1; exact Subtype.ext hprod2.symm
  have hφc : (qb' ≫ ρp.φ) ≫ ρp.Ab.f = Eb'.f := by rw [Category.assoc, hφo, hqb']
  have hφ'c : (ρp.φ' ≫ qb) ≫ Eb'.f = ρp.Ab.f := by rw [Category.assoc, hqb, hφ'o]

  let ρ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr 1 ψ) E' :=
    { Eb := Eb', gb := gb', isPullback_Eb := hEb', Ab := ρp.Ab, gA := ρp.gA, isPullback_Ab := ρp.isPullback_Ab,
      d := ρp.d + 1, φ := qb' ≫ ρp.φ, φ' := ρp.φ' ≫ qb, φ_over := hφc,
      isIsogenyPair := ⟨hφc, hφ'c,
        fun t P Q => by rw [mapPt_mapPt qb' hqb' ρp.φ hφo, mapPt_mapPt qb' hqb' ρp.φ hφo, mapPt_mapPt qb' hqb' ρp.φ hφo,
          qb'_hom, φ_hom],
        fun t P Q => by rw [mapPt_mapPt ρp.φ' hφ'o qb hqb, mapPt_mapPt ρp.φ' hφ'o qb hqb, mapPt_mapPt ρp.φ' hφ'o qb hqb,
          φ'_hom, qb_hom],
        fun x => by rw [← Category.assoc, qb'_act, Category.assoc, φ_act, Category.assoc],
        fun x => by rw [← Category.assoc, φ'_act, Category.assoc, qb_act, Category.assoc],
        fun hd => ⟨by
          calc (qb' ≫ ρp.φ) ≫ ρp.φ' ≫ qb = qb' ≫ (ρp.φ ≫ ρp.φ') ≫ qb := by simp only [Category.assoc]
            _ = qb' ≫ qb ≫ Eb'.act ⟨_, hrd⟩ := by rw [h1, qb_act]
            _ = Eb'.act ⟨_, hd⟩ := by rw [← Category.assoc, hqq2, ← key2 Eb' hd],
          by
          calc (ρp.φ' ≫ qb) ≫ qb' ≫ ρp.φ = ρp.φ' ≫ (qb ≫ qb') ≫ ρp.φ := by simp only [Category.assoc]
            _ = ρp.φ' ≫ ρp.φ ≫ ρp.Ab.act ⟨_, hr⟩ := by rw [hqq1, φ_act]
            _ = ρp.Ab.act ⟨_, hd⟩ := by rw [← Category.assoc, h2, ← key1 ρp.Ab hd]⟩⟩,
      preservesLevel := fun t P hP => by
        rw [mapPt_mapPt qb' hqb' ρp.φ hφo]
        exact ρp.preservesLevel t _ (qb'_lev t P hP) }

  have h1mem : (1 : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ 1
  have e0 : (⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨1, h1mem⟩ := Subtype.ext (by push_cast; simp)
  have e1 : (⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ := Subtype.ext (by push_cast; simp)
  refine ⟨ρ', ub ≫ qb, ?_, ?_, gA', hgA', hgA'pr, Fb, hFb, hFbf, 0, 1, ?_⟩
  · show (ub ≫ qb) ≫ gb' = ρ.gb ≫ q
    rw [Category.assoc, hqg, ← Category.assoc, hub]
  · show (ub ≫ qb) ≫ Eb'.f = ρ.Eb.f
    rw [Category.assoc, hqb, hubf]
  · show (ub ≫ qb) ≫ (qb' ≫ ρp.φ) ≫ ρp.Ab.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ Fb ≫ ρp.Ab.act ⟨(((r ^ 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩
    rw [e0, e1, ρp.Ab.act_one, Category.comp_id]
    calc (ub ≫ qb) ≫ qb' ≫ ρp.φ = ub ≫ (qb ≫ qb') ≫ ρp.φ := by simp only [Category.assoc]
      _ = ub ≫ ρp.φ ≫ ρp.Ab.act ⟨_, hr⟩ := by rw [hqq1, φ_act]
      _ = ρ.φ ≫ Fb ≫ ρp.Ab.act ⟨_, hr⟩ := by rw [← Category.assoc, hφp, Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_frobTwist_one_corr_relFrobenius_of_isAtkinLehnerQuotientVia_of_not_dvd (solution)
