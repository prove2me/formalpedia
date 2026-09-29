-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0dc575c8-dd81-51c8-8e9f-5c261ec38c50

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {N : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {S₀ : Type} [CommRing S₀] (A₀ : FakeEllipticCurve Λ N S₀)
    {Bb : Type} [CommRing Bb] (ψb : S₀ →+* Bb)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of Bb)) (P : SchemeHomOver t' Ab.f)
    (hP : ∃ P₀ : T ⟶ A₀.C, P₀ ≫ A₀.lev = P.1 ≫ gA) :
    FactorsThrough Ab.lev P := by
  obtain ⟨hg, -, -, hlevA⟩ := hAb
  obtain ⟨E', g', hg', -, -, -, hbwd'⟩ := FakeEllipticCurve.exists_isPullback_levelIff ψb A₀

  let e : Ab.A ≅ E'.A := hg.isoIsPullback _ _ hg'
  have he_g : e.hom ≫ g' = gA := by simp [e]
  have he_f : e.hom ≫ E'.f = Ab.f := by simp [e]

  obtain ⟨R₀, hR₀⟩ := hlevA (Ab.lev ≫ Ab.f) ⟨Ab.lev, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩

  obtain ⟨j, hj⟩ := hbwd' (Ab.lev ≫ Ab.f) ⟨Ab.lev ≫ e.hom, by rw [Category.assoc, he_f]⟩
    ⟨R₀, by rw [hR₀]; change _ = (Ab.lev ≫ e.hom) ≫ g'; rw [Category.assoc, he_g]⟩
  change j ≫ E'.lev = Ab.lev ≫ e.hom at hj

  haveI : IsClosedImmersion Ab.lev := Ab.lev_closed
  haveI : IsClosedImmersion E'.lev := E'.lev_closed
  haveI : IsClosedImmersion (j ≫ E'.lev) := by rw [hj]; infer_instance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j E'.lev
  haveI := Ab.lev_finite; haveI := Ab.lev_flat; haveI := Ab.lev_finitePresentation
  haveI := E'.lev_finite; haveI := E'.lev_flat; haveI := E'.lev_finitePresentation
  haveI : IsIso j :=
    isIso_of_isClosedImmersion_of_finrank_eq (Ab.lev ≫ Ab.f) (E'.lev ≫ E'.f) j
      (by rw [← Category.assoc, hj, Category.assoc, he_f]) (fun z => by rw [Ab.lev_rank, E'.lev_rank])

  obtain ⟨P₀, hP₀⟩ := hP
  obtain ⟨q, hq⟩ := hbwd' t' ⟨P.1 ≫ e.hom, by rw [Category.assoc, he_f]; exact P.2⟩
    ⟨P₀, by rw [hP₀]; change _ = (P.1 ≫ e.hom) ≫ g'; rw [Category.assoc, he_g]⟩
  change q ≫ E'.lev = P.1 ≫ e.hom at hq
  refine ⟨q ≫ inv j, ?_⟩
  have hinv : inv j ≫ Ab.lev = E'.lev ≫ e.inv := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hj, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [Category.assoc, hinv, ← Category.assoc, hq, Category.assoc, e.hom_inv_id, Category.comp_id]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia (solution)
