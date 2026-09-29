-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_residueLeg_frobeniusLift_symm_verschiebung_relFrobenius_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/cf178019-757d-5cda-a475-a786e593d84b

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hasFrobeniusVerschiebung_of_prime_not_dvd
import Theorems.Thm_CerednikDrinfeld_isAlgClosed_and_charP_quotient_of_isMaximal_of_forall_monic
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_residueLeg_frobeniusLift_symm_verschiebung_relFrobenius_of_not_dvd
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace P3FrobBaseMinus

universe u

section Points

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}

theorem mapPt_mapPt (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (h : (φ ≫ ψ) ≫ f'' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) h P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

variable (L : GoodReductionJacobian.RelativeGroupLaw R f) (L' : GoodReductionJacobian.RelativeGroupLaw R f')

theorem eq_one_of_mul_self_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x : SchemeHomOver t f}
    (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem mapPt_nsmulPt (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero =>
    show mapPt φ hφ (L.one t) = L'.one t
    exact eq_one_of_mul_self_eq L' t (by rw [← hhom, L.one_mul])
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hhom, ih]

end Points

end P3FrobBaseMinus

open P3FrobBaseMinus GoodReductionJacobian in
theorem solution
    {r N : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) :
    ∃ (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
      (_ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr.symm : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
      (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
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
      (∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀r.A),
        x ≫ V = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x ≫ prA) := by
  obtain ⟨hac, hchar⟩ := CerednikDrinfeld.isAlgClosed_and_charP_quotient_of_isMaximal_of_forall_monic 𝒪 π hunr Onr hOnr_max hOnr_closed
  letI : Field (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := @Ideal.Quotient.field Onr _ (Ideal.span {algebraMap 𝒪 Onr π}) hOnr_max
  haveI : IsAlgClosed (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := hac
  haveI : CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r := hchar
  have hleg : (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) = frobenius (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, FakeEllipticCurve.Rigidification.residueLeg, Ideal.quotientMap_mk, frobenius_def,
      RingHom.coe_coe, ← map_pow]
    exact (Ideal.Quotient.eq).2 (hFr x)
  have hσF : (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)).comp (FakeEllipticCurve.Rigidification.residueLeg π (Fr.symm : Onr →ₐ[𝒪] Onr)) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp [FakeEllipticCurve.Rigidification.residueLeg, Ideal.quotientMap_mk]

  obtain ⟨A₀m, prAm, hpb, hmulm, hactm, hlevm, hlevm'⟩ := FakeEllipticCurve.exists_isPullback_levelIff (FakeEllipticCurve.Rigidification.residueLeg π (Fr.symm : Onr →ₐ[𝒪] Onr)) A₀

  obtain ⟨T, ⟨D⟩⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_hasFrobeniusVerschiebung_of_prime_not_dvd (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r hrN A₀m

  have hcomp : Spec.map (CommRingCat.ofHom (frobenius (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r)) ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π (Fr.symm : Onr →ₐ[𝒪] Onr))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← hleg, ← CommRingCat.ofHom_comp, hσF, CommRingCat.ofHom_id, Spec.map_id]
  have he_over : (D.pr ≫ prAm) ≫ A₀.f = T.f := by
    rw [Category.assoc, hpb.w, ← Category.assoc, D.pr_isPullback.w, Category.assoc, hcomp, Category.comp_id]
  have hsqE : IsPullback (D.pr ≫ prAm) T.f A₀.f (𝟙 _) := by
    have h := D.pr_isPullback.paste_horiz hpb
    rwa [hcomp] at h
  obtain ⟨s, hs₁, hs₂⟩ : ∃ s : A₀.A ⟶ T.A, s ≫ (D.pr ≫ prAm) = 𝟙 _ ∧ s ≫ T.f = A₀.f :=
    ⟨hsqE.lift (𝟙 _) A₀.f (by rw [Category.id_comp, Category.comp_id]), hsqE.lift_fst _ _ _, hsqE.lift_snd _ _ _⟩
  have hes : (D.pr ≫ prAm) ≫ s = 𝟙 _ := by
    apply hsqE.hom_ext
    · rw [Category.assoc, hs₁, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hs₂, he_over, Category.id_comp]

  have hse_pt : ∀ {U : Scheme.{0}} (t : U ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      mapPt (D.pr ≫ prAm) he_over (mapPt s hs₂ P) = P := fun t P =>
    Subtype.ext (by simp only [mapPt_coe, Category.assoc, hs₁, Category.comp_id])
  have hes_pt : ∀ {U : Scheme.{0}} (t : U ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t T.f),
      mapPt s hs₂ (mapPt (D.pr ≫ prAm) he_over Q) = Q := fun t Q =>
    Subtype.ext (by rw [mapPt_coe, mapPt_coe, Category.assoc, hes, Category.comp_id])
  have e_hom : ∀ {U : Scheme.{0}} (t : U ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t T.f),
      mapPt (D.pr ≫ prAm) he_over (T.L.mul t P Q) = A₀.L.mul t (mapPt (D.pr ≫ prAm) he_over P) (mapPt (D.pr ≫ prAm) he_over Q) := by
    intro U t P Q
    apply Subtype.ext
    rw [mapPt_coe, ← Category.assoc, D.pr_mul, hmulm]
    exact mul_val_congr A₀.L (by rw [Category.assoc, hcomp, Category.comp_id]) _ _ _ _
      (by simp only [mapPt_coe, Category.assoc]) (by simp only [mapPt_coe, Category.assoc])
  have s_hom : ∀ {U : Scheme.{0}} (t : U ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
      mapPt s hs₂ (A₀.L.mul t P Q) = T.L.mul t (mapPt s hs₂ P) (mapPt s hs₂ Q) := by
    intro U t P Q
    rw [← hes_pt t (T.L.mul t _ _), e_hom, hse_pt, hse_pt]
  have e_act : ∀ x : ↥Λ, T.act x ≫ (D.pr ≫ prAm) = (D.pr ≫ prAm) ≫ A₀.act x := fun x => by
    rw [← Category.assoc, D.pr_act, Category.assoc, hactm, Category.assoc]
  have hes' : D.pr ≫ prAm ≫ s = 𝟙 _ := by simpa only [Category.assoc] using hes
  have s_act : ∀ x : ↥Λ, A₀.act x ≫ s = s ≫ T.act x := fun x => by
    calc A₀.act x ≫ s = (s ≫ (D.pr ≫ prAm)) ≫ A₀.act x ≫ s := by rw [hs₁, Category.id_comp]
      _ = s ≫ (T.act x ≫ (D.pr ≫ prAm)) ≫ s := by rw [e_act]; simp only [Category.assoc]
      _ = s ≫ T.act x := by simp only [Category.assoc, hes', Category.comp_id]
  have e_lev : ∀ {U : Scheme.{0}} (t : U ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t T.f),
      FactorsThrough T.lev P → FactorsThrough A₀.lev (mapPt (D.pr ≫ prAm) he_over P) := by
    intro U t P hP
    obtain ⟨P₀, hP₀⟩ := D.pr_lev t P hP
    obtain ⟨P₁, hP₁⟩ := hlevm (t ≫ Spec.map (CommRingCat.ofHom (frobenius (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r)))
      ⟨P.1 ≫ D.pr, by rw [Category.assoc, D.pr_isPullback.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    exact ⟨P₁, by rw [hP₁]; simp only [mapPt_coe, Category.assoc]⟩
  have e_lev_iff : ∀ {U : Scheme.{0}} (t : U ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev Q ↔ ∃ P : SchemeHomOver t T.f, FactorsThrough T.lev P ∧ mapPt (D.pr ≫ prAm) he_over P = Q :=
    fun t Q => CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime T A₀ (D.pr ≫ prAm) he_over
      e_hom s hs₂ 1 (Nat.coprime_one_left N)
      (fun t P => by
        show mapPt s hs₂ (mapPt (D.pr ≫ prAm) he_over P) = T.L.mul t (T.L.one t) P
        rw [T.L.one_mul, hes_pt])
      e_lev t Q

  have hG : (s ≫ D.V) ≫ A₀m.f = A₀.f := by rw [Category.assoc, D.V_over, hs₂]
  have hH : (D.F ≫ (D.pr ≫ prAm)) ≫ A₀.f = A₀m.f := by rw [Category.assoc, he_over, D.F_over]
  refine ⟨A₀m, prAm, ⟨hpb, hmulm, hactm, hlevm⟩, s ≫ D.V, hG, D.F ≫ (D.pr ≫ prAm), hH, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro U t P Q
    rw [← mapPt_mapPt s hs₂ D.V D.V_over hG, ← mapPt_mapPt s hs₂ D.V D.V_over hG, ← mapPt_mapPt s hs₂ D.V D.V_over hG,
      s_hom, D.V_hom]
  ·
    intro U t P Q
    rw [← mapPt_mapPt D.F D.F_over (D.pr ≫ prAm) he_over hH, ← mapPt_mapPt D.F D.F_over (D.pr ≫ prAm) he_over hH,
      ← mapPt_mapPt D.F D.F_over (D.pr ≫ prAm) he_over hH, D.F_hom, e_hom]
  ·
    intro x
    rw [← Category.assoc, s_act, Category.assoc, D.V_act, Category.assoc]
  ·
    intro x
    rw [← Category.assoc, D.F_act, Category.assoc, e_act]; simp only [Category.assoc]
  ·
    intro U t P hP
    obtain ⟨P', hP', hP'e⟩ := (e_lev_iff t P).1 hP
    have hsP : mapPt s hs₂ P = P' := by rw [← hP'e, hes_pt]
    rw [← mapPt_mapPt s hs₂ D.V D.V_over hG, hsP]
    exact D.V_lev t P' hP'
  ·
    intro U t Q hQ
    rw [← mapPt_mapPt D.F D.F_over (D.pr ≫ prAm) he_over hH]
    exact e_lev t _ (D.F_lev t Q hQ)
  ·
    intro U t P
    rw [← mapPt_mapPt s hs₂ D.V D.V_over hG, ← mapPt_mapPt D.F D.F_over (D.pr ≫ prAm) he_over hH, D.F_V,
      mapPt_nsmulPt T.L A₀.L (D.pr ≫ prAm) he_over e_hom, hse_pt]
  ·
    intro U t Q
    rw [← mapPt_mapPt D.F D.F_over (D.pr ≫ prAm) he_over hH, ← mapPt_mapPt s hs₂ D.V D.V_over hG, hes_pt, D.V_F]
  ·
    intro C _ _ x
    calc x ≫ D.F ≫ (D.pr ≫ prAm) = (x ≫ D.F ≫ D.pr) ≫ prAm := by simp only [Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x) ≫ prAm := by rw [D.F_frobenius]
      _ = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x ≫ prAm := by rw [Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_residueLeg_frobeniusLift_symm_verschiebung_relFrobenius_of_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_residueLeg_frobeniusLift_symm_verschiebung_relFrobenius_of_not_dvd (solution)
