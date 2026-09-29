-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_iff_of_forall_geomPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f684b0be-df0a-54af-85bb-ad70962bc985

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp"
open CategoryTheory.Limits GoodReductionJacobian

namespace ExtraLevelExtGC3

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

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

variable (E : FakeEllipticCurve Λ N S) {ℓ : ℕ}

theorem levK_comp_schemeNsmul (K : E.ExtraLevel ℓ) :
    K.levK ≫ E.L.schemeNsmul ℓ = (K.levK ≫ E.f) ≫ (E.L.one (𝟙 _)).1 := by
  have ht := K.levK_torsion (K.levK ≫ E.f) ⟨K.levK, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
  have := congrArg Subtype.val ht
  rw [nsmulPt_coe, one_coe] at this
  exact this

noncomputable def jK (K : E.ExtraLevel ℓ) : K.K ⟶ E.L.schemeKer ℓ :=
  pullback.lift K.levK (K.levK ≫ E.f) (levK_comp_schemeNsmul E K)

@[scoped simp] theorem jK_fst (K : E.ExtraLevel ℓ) : jK E K ≫ pullback.fst _ _ = K.levK := pullback.lift_fst _ _ _
@[scoped simp] theorem jK_snd (K : E.ExtraLevel ℓ) : jK E K ≫ E.L.schemeKerStr ℓ = K.levK ≫ E.f := pullback.lift_snd _ _ _

theorem isClosedImmersion_one : IsClosedImmersion (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  haveI : IsProper E.f := E.bundle.proper
  haveI : IsClosedImmersion ((E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f) := by
    rw [(E.L.one (𝟙 (Spec (CommRingCat.of S)))).2]; infer_instance
  exact IsClosedImmersion.of_comp _ E.f

theorem isOpenImmersion_jK (hℓS : IsUnit ((ℓ : ℕ) : S)) (K : E.ExtraLevel ℓ) : IsOpenImmersion (jK E K) := by
  haveI := isClosedImmersion_one E
  haveI : IsClosedImmersion (jK E K ≫ pullback.fst (E.L.schemeNsmul ℓ) (E.L.one (𝟙 _)).1) := by
    rw [jK_fst]; exact K.levK_closed
  haveI : IsClosedImmersion (jK E K) := IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.fst _ _)
  haveI : Etale (E.L.schemeKerStr ℓ) := (CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E ℓ hℓS).2
  haveI : Flat (jK E K ≫ E.L.schemeKerStr ℓ) := by rw [jK_snd]; exact K.levK_flat
  haveI : LocallyOfFinitePresentation (jK E K ≫ E.L.schemeKerStr ℓ) := by rw [jK_snd]; exact K.levK_finitePresentation
  exact (AlgebraicGeometry.IsOpenImmersion.of_isClosedImmersion_of_flat_comp_of_etale (jK E K) (E.L.schemeKerStr ℓ)).1

theorem range_jK_subset (K K' : E.ExtraLevel ℓ)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough K.levK Q → FactorsThrough K'.levK Q) :
    Set.range (jK E K).base ⊆ Set.range (jK E K').base := by
  haveI := isClosedImmersion_one E
  rintro _ ⟨x, rfl⟩

  let κ : Type := K.K.residueField x
  let kb : Type := AlgebraicClosure κ
  let g₀ : Spec (CommRingCat.of kb) ⟶ K.K := Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ K.K.fromSpecResidueField x
  have hg₀ : ∀ p, g₀.base p = x := fun p => by
    show (K.K.fromSpecResidueField x).base ((Spec.map (CommRingCat.ofHom (algebraMap κ kb))).base p) = x
    exact Scheme.fromSpecResidueField_apply x _
  let q : Spec (CommRingCat.of kb) ⟶ E.A := g₀ ≫ K.levK
  let sk : S →+* kb := (Spec.preimage (q ≫ E.f)).hom
  have hq : q ≫ E.f = geomPoint kb sk := by
    show q ≫ E.f = Spec.map (CommRingCat.ofHom (Spec.preimage (q ≫ E.f)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨Q₀', hQ₀'⟩ := h kb sk ⟨q, hq⟩ ⟨g₀, rfl⟩
  let p : Spec (CommRingCat.of kb) := IsLocalRing.closedPoint kb
  refine ⟨Q₀'.base p, ?_⟩
  apply (pullback.fst (E.L.schemeNsmul ℓ) (E.L.one (𝟙 _)).1).isClosedEmbedding.injective
  have lhs : (pullback.fst (E.L.schemeNsmul ℓ) (E.L.one (𝟙 _)).1).base ((jK E K').base (Q₀'.base p)) = K.levK.base x := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, jK_fst, hQ₀']
    show (g₀ ≫ K.levK).base p = _
    rw [Scheme.Hom.comp_apply, hg₀]
  have rhs : (pullback.fst (E.L.schemeNsmul ℓ) (E.L.one (𝟙 _)).1).base ((jK E K).base x) = K.levK.base x := by
    rw [← Scheme.Hom.comp_apply, jK_fst]
  exact lhs.trans rhs.symm

theorem factorsThrough_of (hℓS : IsUnit ((ℓ : ℕ) : S)) (K K' : E.ExtraLevel ℓ)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough K.levK Q → FactorsThrough K'.levK Q)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f) (hQ : FactorsThrough K.levK Q) :
    FactorsThrough K'.levK Q := by
  obtain ⟨Q₀, hQ₀⟩ := hQ
  haveI := isOpenImmersion_jK E hℓS K'
  have H' : Set.range (Q₀ ≫ jK E K).base ⊆ Set.range (jK E K').base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact range_jK_subset E K K' h ⟨_, rfl⟩
  refine ⟨IsOpenImmersion.lift (jK E K') (Q₀ ≫ jK E K) H', ?_⟩
  rw [← jK_fst E K', ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, jK_fst, hQ₀]

end ExtraLevelExtGC3
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint.ExtraLevelExtGC3"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (ℓ : ℕ) (hℓ : ℓ.Prime)
    {S : Type} [CommRing S] (hℓS : IsUnit ((ℓ : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (K K' : E.ExtraLevel ℓ)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough K.levK Q ↔ FactorsThrough K'.levK Q)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f) :
    FactorsThrough K.levK Q ↔ FactorsThrough K'.levK Q := by
  exact ⟨ExtraLevelExtGC3.factorsThrough_of E hℓS K K' (fun k _ _ sk Q => (h k sk Q).1) t Q,
    ExtraLevelExtGC3.factorsThrough_of E hℓS K' K (fun k _ _ sk Q => (h k sk Q).2) t Q⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint (solution)
