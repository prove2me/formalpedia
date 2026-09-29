-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_hasFrobeniusVerschiebung_of_prime_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6c8174d8-a5a6-511e-ae51-3231098af98f

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_relFrobenius_of_isPullback_frobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_relFrobenius_of_flat
import Theorems.Thm_AlgebraicGeometry_Smooth_isFinite_and_flat_and_surjective_of_isPullback_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hasFrobeniusVerschiebung_of_prime_not_dvd
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (E : FakeEllipticCurve Λ N k) :
    ∃ Eℓ : FakeEllipticCurve Λ N k, FakeEllipticCurve.HasFrobeniusVerschiebung ℓ E Eℓ := by
  obtain ⟨Eℓ, pr, hpr, hmul, hact, hlev, hlev'⟩ := exists_isPullback_levelIff (frobenius k ℓ) E
  have hS : (ℓ : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero k ℓ)
  have hA : (ℓ : Γ(E.A, ⊤)) = 0 := by
    rw [← map_natCast E.f.appTop.hom ℓ, hS, map_zero]
  haveI : Smooth E.f := E.bundle.smooth
  obtain ⟨F, hF, hFpr, hpin, hhom, hFact, hFlev⟩ :=
    exists_relFrobenius_of_isPullback_frobenius k ℓ E Eℓ pr hpr hmul hact hlev hlev' hA
  obtain ⟨hfin, hflat, -, hsurj⟩ :=
    AlgebraicGeometry.Smooth.isFinite_and_flat_and_surjective_of_isPullback_frobenius k ℓ E.f Eℓ.f pr hpr F hF hpin
  haveI := hfin; haveI := hflat; haveI := hsurj
  exact ⟨Eℓ, hasFrobeniusVerschiebung_of_relFrobenius_of_flat k ℓ E Eℓ pr hpr hmul hact hlev hlev' hA F hF hFpr hhom
    hFact hFlev hℓN⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hasFrobeniusVerschiebung_of_prime_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hasFrobeniusVerschiebung_of_prime_not_dvd (solution)
