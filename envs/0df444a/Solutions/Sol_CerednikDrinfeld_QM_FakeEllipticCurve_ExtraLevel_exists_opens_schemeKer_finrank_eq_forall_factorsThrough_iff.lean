-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/078d5744-bf01-5acd-afe9-962707e8b713

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N' : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N' S) (N : ℕ) (hN : IsUnit ((N : ℕ) : S)) (K : E.ExtraLevel N) :
    ∃ U : (E.L.schemeKer N).Opens, IsClosed (U : Set ↥(E.L.schemeKer N)) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), (U.ι ≫ E.L.schemeKerStr N).finrank s = N ^ 2) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P := by
  classical
  obtain ⟨-, hEt⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E N hN
  haveI := hEt
  haveI := K.levK_closed
  haveI := K.levK_flat
  haveI := K.levK_finitePresentation
  haveI := K.levK_finite
  obtain ⟨U, e, hUcl, he, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
      E.L N K.levK (fun t P h => K.levK_torsion t P h)

  have hfst : pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f =
      E.L.schemeKerStr N := by
    calc pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ E.f
        = pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ (E.L.schemeNsmul N ≫ E.f) := by
          rw [E.L.schemeNsmul_over N]
      _ = (pullback.snd (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫
            (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ E.f := by
          rw [← Category.assoc, pullback.condition]
      _ = E.L.schemeKerStr N := by
          rw [Category.assoc, (E.L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id]
  refine ⟨U, hUcl, ?_, ?_⟩
  ·
    intro s
    have hg : U.ι ≫ E.L.schemeKerStr N = e.inv ≫ (K.levK ≫ E.f) := by
      rw [← he, Category.assoc, Category.assoc, hfst, Iso.inv_hom_id_assoc]
    rw [hg, Scheme.Hom.finrank_comp_left_of_isIso, K.levK_rank s]
  ·
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      exact ⟨P₀ ≫ e.hom, by rw [← hP₀, ← he, Category.assoc]⟩
    · rintro ⟨P₀, hP₀⟩
      exact ⟨P₀ ≫ e.inv, by rw [← hP₀, ← he, Category.assoc, Iso.inv_hom_id_assoc]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_opens_schemeKer_finrank_eq_forall_factorsThrough_iff (solution)
