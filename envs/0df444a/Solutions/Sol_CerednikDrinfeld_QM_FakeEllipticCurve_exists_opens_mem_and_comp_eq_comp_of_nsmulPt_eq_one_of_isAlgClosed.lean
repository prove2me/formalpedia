-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_opens_mem_and_comp_eq_comp_of_nsmulPt_eq_one_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/464d17fe-2b17-50c6-9fae-981e144a001c

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_sectionAt_eq_of_nsmulPt_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_mem_and_comp_eq_comp_of_nsmulPt_eq_one_of_isAlgClosed
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra"
open scoped Quaternion

namespace P8LocConst

variable {S : Type} [CommRing S]

theorem nsmulPt_eq_nsmul {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmulPt_coe {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  rw [nsmulPt_eq_nsmul]
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (Category.comp_id _)
  have := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  rw [hP] at this
  rw [← this]
  rfl

theorem one_coe {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have := L.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← this]
  rfl

theorem nsmulPt_comp_eq_one {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) (hP : nsmulPt L t n P = L.one t) :
    nsmulPt L t' n (schemeHomOverComp ψ hψ P) = L.one t' := by
  rw [nsmulPt_eq_nsmul] at hP ⊢
  rw [← L.nsmul_natural t t' ψ hψ n P, hP]
  exact L.one_natural t t' ψ hψ

end P8LocConst

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (E : FakeEllipticCurve Λ N k₀) (n : ℕ) (hn : (n : k₀) ≠ 0)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t n P = E.L.one t) (x : ↥T) :
    ∃ U : T.Opens, x ∈ U ∧ ∃ Q₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k₀))) n Q₀ = E.L.one (𝟙 (Spec (CommRingCat.of k₀))) ∧
      U.ι ≫ P.1 = (U.ι ≫ t) ≫ Q₀.1 := by
  classical
  haveI : IsAlgClosed k₀ := inferInstance
  have hnu : IsUnit ((n : ℕ) : k₀) := (Ne.isUnit hn)

  haveI hEt : Etale (E.L.schemeKerStr n) := (CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E n hnu).2

  haveI hone : IsClosedImmersion (E.L.one (𝟙 (Spec (CommRingCat.of k₀)))).1 := by
    haveI : IsProper E.f := E.bundle.proper
    haveI : IsClosedImmersion ((E.L.one (𝟙 (Spec (CommRingCat.of k₀)))).1 ≫ E.f) := by
      rw [(E.L.one (𝟙 (Spec (CommRingCat.of k₀)))).2]; infer_instance
    exact IsClosedImmersion.of_comp _ E.f

  have hw : P.1 ≫ E.L.schemeNsmul n = t ≫ (E.L.one (𝟙 (Spec (CommRingCat.of k₀)))).1 := by
    rw [← P8LocConst.nsmulPt_coe, hP, P8LocConst.one_coe]
  let Pt : T ⟶ E.L.schemeKer n := pullback.lift P.1 t hw
  have hPt : Pt ≫ pullback.fst _ _ = P.1 := pullback.lift_fst _ _ _

  let ρ : Spec (T.residueField x) ⟶ T := T.fromSpecResidueField x
  let sk : k₀ →+* T.residueField x := (Spec.preimage (ρ ≫ t)).hom
  have hρ : ρ ≫ t = geomPoint (T.residueField x) sk := by
    show ρ ≫ t = Spec.map (CommRingCat.ofHom (Spec.preimage (ρ ≫ t)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let Q : SchemeHomOver (geomPoint (T.residueField x) sk) E.f := schemeHomOverComp ρ hρ P
  have hQ : nsmulPt E.L (geomPoint (T.residueField x) sk) n Q = E.L.one _ :=
    P8LocConst.nsmulPt_comp_eq_one E.L t _ ρ hρ n P hP
  obtain ⟨Q₀, ⟨hQ₀, hQ₀Q⟩, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_sectionAt_eq_of_nsmulPt_eq_one k₀ E n hn (T.residueField x) sk Q hQ

  have hx_im : ∃ w : ↥(Spec (CommRingCat.of k₀)), Q₀.1.base w = P.1.base x := by
    let c : ↥(Spec (CommRingCat.of (T.residueField x))) := IsLocalRing.closedPoint (T.residueField x)
    refine ⟨(geomPoint (T.residueField x) sk).base c, ?_⟩
    have h1 : (FakeEllipticCurve.sectionAt Q₀ (T.residueField x) sk).1 = geomPoint (T.residueField x) sk ≫ Q₀.1 := rfl
    have h2 := congrArg Subtype.val hQ₀Q
    rw [h1] at h2
    rw [← Scheme.Hom.comp_apply, h2]
    show (ρ ≫ P.1).base c = P.1.base x
    rw [Scheme.Hom.comp_apply]
    exact congrArg P.1.base (Scheme.fromSpecResidueField_apply x c)

  haveI : IsClosedImmersion Q₀.1 := by
    haveI : IsProper E.f := E.bundle.proper
    haveI : IsClosedImmersion (Q₀.1 ≫ E.f) := by rw [Q₀.2]; infer_instance
    exact IsClosedImmersion.of_comp _ E.f
  haveI : Flat (Q₀.1 ≫ E.f) := by rw [Q₀.2]; infer_instance
  haveI : LocallyOfFinitePresentation (Q₀.1 ≫ E.f) := by rw [Q₀.2]; infer_instance
  have htor : ∀ {T' : Scheme.{0}} (t' : T' ⟶ Spec (CommRingCat.of k₀)) (P' : SchemeHomOver t' E.f),
      FactorsThrough Q₀.1 P' → nsmulPt E.L t' n P' = E.L.one t' := by
    intro T' t' P' ⟨P₁, hP₁⟩
    have ht' : P₁ ≫ 𝟙 _ = t' := by rw [Category.comp_id, ← P'.2, ← hP₁, Category.assoc, Q₀.2, Category.comp_id]
    have hP' : P' = schemeHomOverComp P₁ ht' Q₀ := Subtype.ext hP₁.symm
    rw [hP']
    exact P8LocConst.nsmulPt_comp_eq_one E.L _ _ P₁ ht' n Q₀ hQ₀
  obtain ⟨U, e, -, heU, hiff⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one E.L n Q₀.1 htor

  have hxU : Pt.base x ∈ (U : Set ↥(E.L.schemeKer n)) := by
    obtain ⟨w, hw⟩ := hx_im
    have hinj := (pullback.fst (E.L.schemeNsmul n) (E.L.one (𝟙 (Spec (CommRingCat.of k₀)))).1).isClosedEmbedding.injective
    have key : (pullback.fst (E.L.schemeNsmul n) (E.L.one (𝟙 (Spec (CommRingCat.of k₀)))).1).base ((e.hom ≫ U.ι).base w) =
        (pullback.fst (E.L.schemeNsmul n) (E.L.one (𝟙 (Spec (CommRingCat.of k₀)))).1).base (Pt.base x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, heU, hPt, hw]
    rw [← hinj key, Scheme.Hom.comp_apply]
    have hmem : U.ι.base (e.hom.base w) ∈ Set.range U.ι.base := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at hmem

  refine ⟨Pt ⁻¹ᵁ U, hxU, Q₀, hQ₀, ?_⟩
  let P' : SchemeHomOver ((Pt ⁻¹ᵁ U).ι ≫ t) E.f := ⟨(Pt ⁻¹ᵁ U).ι ≫ P.1, by rw [Category.assoc, P.2]⟩
  have hfac : FactorsThrough Q₀.1 P' := by
    refine (hiff ((Pt ⁻¹ᵁ U).ι ≫ t) P').2 ⟨(Pt ⁻¹ᵁ U).ι ≫ Pt, ?_, ?_⟩
    · rw [Category.assoc, hPt]
    · rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact u.2
  obtain ⟨P₁, hP₁⟩ := hfac
  have hP₁t : P₁ = (Pt ⁻¹ᵁ U).ι ≫ t := by
    rw [← Category.comp_id P₁, ← Q₀.2, ← Category.assoc, hP₁]
    show ((Pt ⁻¹ᵁ U).ι ≫ P.1) ≫ E.f = _
    rw [Category.assoc, P.2]
  rw [← hP₁t, hP₁]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_mem_and_comp_eq_comp_of_nsmulPt_eq_one_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_mem_and_comp_eq_comp_of_nsmulPt_eq_one_of_isAlgClosed (solution)
