-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/68273b13-291e-59f2-97e2-125902bfccad

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {N : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {k₀ : Type} [Field k₀] (A₀ : FakeEllipticCurve Λ N k₀)
    {Bb : Type} [CommRing Bb] [Nontrivial Bb] (ψb : k₀ →+* Bb)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)
    (φ : Ab.A ⟶ Ab.A) (hφ : φ ≫ Ab.f = Ab.f) (φ₀ : A₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = A₀.f)
    (hφg : φ ≫ gA = gA ≫ φ₀)
    (hlev : FakeEllipticCurve.PreservesLevel Ab Ab φ hφ) :
    FakeEllipticCurve.PreservesLevel A₀ A₀ φ₀ hφ₀ := by
  intro T t P hP
  obtain ⟨P₀, hP₀⟩ := hP
  have hAb' := hAb
  obtain ⟨hg, -, -, hlevA⟩ := hAb'

  set sb := Spec.map (CommRingCat.ofHom ψb) with hsb
  let π := pullback.fst t sb
  let t' := pullback.snd t sb
  have w : (π ≫ P.1) ≫ A₀.f = t' ≫ sb := by rw [Category.assoc, P.2]; exact pullback.condition
  let P' : SchemeHomOver t' Ab.f := ⟨hg.lift (π ≫ P.1) t' w, hg.lift_snd _ _ _⟩
  have hP'g : P'.1 ≫ gA = π ≫ P.1 := hg.lift_fst _ _ _

  have hP'lev : FactorsThrough Ab.lev P' :=
    CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia A₀ ψb Ab gA
      hAb t' P' ⟨π ≫ P₀, by rw [Category.assoc, hP₀, hP'g]⟩

  have h1 : FactorsThrough Ab.lev (mapPt φ hφ P') := hlev t' P' hP'lev
  obtain ⟨Q', hQ'⟩ := hlevA t' (mapPt φ hφ P') h1

  haveI : IsClosedImmersion A₀.lev := A₀.lev_closed
  have hπ : π.ker = ⊥ := AlgebraicGeometry.Scheme.Hom.ker_pullback_fst_specMap_eq_bot_of_field ψb t
  obtain ⟨z, hz⟩ := AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_of_exists_comp_eq_comp_of_ker_eq_bot
    π hπ (P.1 ≫ φ₀) A₀.lev ⟨Q', by rw [hQ', mapPt_coe, Category.assoc, hφg, ← Category.assoc, hP'g, Category.assoc]⟩
  exact ⟨z, by rw [hz, mapPt_coe]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_preservesLevel_of_comp_eq_comp_of_isPullbackVia (solution)
