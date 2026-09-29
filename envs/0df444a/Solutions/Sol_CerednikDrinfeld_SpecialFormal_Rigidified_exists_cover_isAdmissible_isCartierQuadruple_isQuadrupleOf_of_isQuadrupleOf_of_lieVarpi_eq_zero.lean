-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/aea559db-6f1a-57f0-914b-1631efd4c8d3

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isPeriodMap_of_lieVarpi_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_isNoetherianRing_of_lieVarpi_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient MvFormalGroup.CartierModule.instModulePadicInt MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite"
p2m_attr_erase "instance" "CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq"
p2m_attr_erase "simp" "CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj CerednikDrinfeld.FormalOmega.AlgFunctor.algHomOfComp_apply CerednikDrinfeld.FormalOmega.AlgFunctor.toModuliPackage_obj AlgebraicGeometry.Scheme.nilpPoints_map_val CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst CerednikDrinfeld.FormalODModule.frobTwist_F CerednikDrinfeld.FormalODModule.frobTwist_frobTwist CerednikDrinfeld.FormalODModule.frobTwist_varpi CerednikDrinfeld.FormalODModule.frobTwist_act ModpDieudonneRealization.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    :
    (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B), Q.IsQuadrupleOf d →
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] B L]
        [IsLocalization.Away (f i) L] (hL : IsNilpotent (p : L)),
        ∃ (t : Rigidified p Φ L) (dL : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) L)
          (QL : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) L),
          t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
          t.IsCartierQuadruple ι hcΦ rΦ ((algebraMap B L).comp ψ) QL ∧ QL.IsQuadrupleOf dL ∧
          DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) (IsScalarTower.toAlgHom ℤ_[p] B L) d dL) := by
  intro B _ _ _ ψ hB Q d hQd
  classical

  obtain ⟨M, hM, η, hη⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover p k ι Φ hΦ hΦ4
  obtain ⟨θ, hθ⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isPeriodMap_of_lieVarpi_eq_zero p k ι Φ hΦ hΦ4 h0 M hM η hη hcΦ rΦ hrΦ
  obtain ⟨LΦ, hLΦ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed p k ι Φ hΦ hcΦ

  obtain ⟨m, hm⟩ := (CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isNoetherianRing_of_lieVarpi_eq_zero p k ι Φ hΦ hΦ4 h0 M hM η hη hcΦ rΦ hrΦ θ hθ B ψ hB).2 d

  obtain ⟨n, f, hf, hloc⟩ := hη.2.2 B ψ hB m
  refine ⟨n, f, hf, fun i L _ _ _ _ _ _ hL => ?_⟩
  obtain ⟨t, ht, hηt⟩ := hloc i L hL

  obtain ⟨QL, hQL⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector p k ι Φ hΦ hΦ4 (fun m hm => LinearMap.mem_ker.mpr (h0 m hm)) hcΦ rΦ ⟨LΦ, hLΦ⟩ hrΦ
    ((algebraMap B L).comp ψ) hL t ht
  refine ⟨t, d.map (p : ℤ_[p]) (IsScalarTower.toAlgHom ℤ_[p] B L), QL, ht, hQL, ?_,
    DeligneDatum.isBaseChange_map _ _ _⟩

  have h1 := hθ.1 L ((algebraMap B L).comp ψ) hL t ht QL hQL
  have h2 := hθ.2 B L ψ ((algebraMap B L).comp ψ) hB hL (IsScalarTower.toAlgHom ℤ_[p] B L) rfl m
  have h3 : θ L ((algebraMap B L).comp ψ) hL (M.map hB hL (algebraMap B L) rfl m) =
      d.map (p : ℤ_[p]) (IsScalarTower.toAlgHom ℤ_[p] B L) := by
    rw [← hm]
    exact DeligneDatum.ext' (funext fun N => h2 N)
  rw [hηt, h3] at h1
  exact h1

#print axioms solution

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero (solution)
