-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ab96639b-2a7c-55fb-99dc-6e9220aaaa0b

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
import Theorems.Thm_AlgebraicGeometry_finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace S1Body

theorem exists_geomPoint_apply_eq {S : Type} [CommRing S] (s : ↥(Spec (CommRingCat.of S))) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (sk : S →+* k),
      (Spec.map (CommRingCat.ofHom sk)).base (IsLocalRing.closedPoint k) = s := by
  let K := s.asIdeal.ResidueField
  let k := AlgebraicClosure K
  refine ⟨k, inferInstance, inferInstance, (algebraMap K k).comp (algebraMap S K), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap ((algebraMap K k).comp (algebraMap S K)) (IsLocalRing.closedPoint k).asIdeal = s.asIdeal
  have h1 : (IsLocalRing.closedPoint k).asIdeal = ⊥ := by
    change IsLocalRing.maximalIdeal k = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  rw [h1, ← RingHom.ker_eq_comap_bot, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap K k).injective,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end S1Body

open S1Body in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ}
    (S : Type) [CommRing S] (hM : IsUnit ((M : ℕ) : S)) (E : FakeEllipticCurve Λ M S) (n : ℕ) (hn : n ∣ M) :
    ∃ (Cn : Scheme.{0}) (levn : Cn ⟶ E.A), IsClosedImmersion levn ∧
      IsFinite (levn ≫ E.f) ∧ Flat (levn ≫ E.f) ∧ LocallyOfFinitePresentation (levn ≫ E.f) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), (levn ≫ E.f).finrank s = n ^ 2) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        FactorsThrough levn P ↔ FactorsThrough E.lev P ∧ nsmulPt E.L t n P = E.L.one t := by
  classical

  set ι : E.L.schemeKer n ⟶ E.A := pullback.fst (E.L.schemeNsmul n) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 with hι
  obtain ⟨hfin, het, hopen, hpts⟩ :=
    CerednikDrinfeld.QM.isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
      E.L E.comm E.bundle E.lev E.lev_closed M E.lev_torsion E.lev_flat E.lev_finitePresentation hM n hn

  haveI : IsClosedImmersion E.lev := E.lev_closed
  haveI : IsProper E.f := E.bundle.proper
  have hone : IsClosedImmersion (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    have : IsClosedImmersion ((E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f) := by
      rw [(E.L.one (𝟙 (Spec (CommRingCat.of S)))).2]; infer_instance
    exact IsClosedImmersion.of_comp _ E.f
  haveI : IsClosedImmersion ι := MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ hone
  have hclosed : IsClosedImmersion (pullback.fst E.lev ι ≫ E.lev) := by
    rw [pullback.condition]; infer_instance
  refine ⟨pullback E.lev ι, pullback.fst E.lev ι ≫ E.lev, hclosed, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact hfin
  · haveI := het; rw [Category.assoc]; infer_instance
  · haveI := het; rw [Category.assoc]; infer_instance
  ·
    intro s
    obtain ⟨k, _, _, sk, hs⟩ := exists_geomPoint_apply_eq s
    haveI : IsFinite ((pullback.fst E.lev ι ≫ E.lev) ≫ E.f) := by rw [Category.assoc]; exact hfin
    haveI : Etale ((pullback.fst E.lev ι ≫ E.lev) ≫ E.f) := by rw [Category.assoc]; exact het
    rw [← hs, AlgebraicGeometry.finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed _ k sk]

    have hk : ((M : ℕ) : k) ≠ 0 := by
      have : IsUnit ((M : ℕ) : k) := by simpa using hM.map sk
      intro h0
      rw [h0] at this
      exact not_isUnit_zero this
    obtain ⟨e, -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_lev_and_nsmulPt_eq_one_of_dvd
        Λ S E n hn k sk hk

    haveI : Mono (pullback.fst E.lev ι ≫ E.lev) := inferInstance
    let F : {w : Spec (CommRingCat.of k) ⟶ pullback E.lev ι // w ≫ (pullback.fst E.lev ι ≫ E.lev) ≫ E.f = Spec.map (CommRingCat.ofHom sk)} →
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough E.lev P ∧ nsmulPt E.L (geomPoint k sk) n P = E.L.one (geomPoint k sk)} :=
      fun w => ⟨⟨w.1 ≫ (pullback.fst E.lev ι ≫ E.lev), by rw [Category.assoc]; exact w.2⟩,
        (hpts (geomPoint k sk) ⟨w.1 ≫ (pullback.fst E.lev ι ≫ E.lev), by rw [Category.assoc]; exact w.2⟩).mp ⟨w.1, rfl⟩⟩
    have hF : Function.Bijective F := by
      constructor
      · intro w w' h
        apply Subtype.ext
        have h' := congrArg (fun P => P.1.1) h
        exact (cancel_mono (pullback.fst E.lev ι ≫ E.lev)).mp h'
      · intro P
        obtain ⟨P₀, hP₀⟩ := (hpts (geomPoint k sk) P.1).mpr P.2
        refine ⟨⟨P₀, ?_⟩, ?_⟩
        · rw [← Category.assoc, hP₀]; exact P.1.2
        · apply Subtype.ext; apply Subtype.ext; exact hP₀
    rw [Nat.card_eq_of_bijective F hF, ← Nat.card_eq_of_bijective e e.bijective, Nat.card_prod, Nat.card_zmod, pow_two]
  · intro T t P
    exact hpts t P

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClosedImmersion_finrank_eq_sq_forall_factorsThrough_iff_nsmulPt_of_dvd_of_isUnit (solution)
