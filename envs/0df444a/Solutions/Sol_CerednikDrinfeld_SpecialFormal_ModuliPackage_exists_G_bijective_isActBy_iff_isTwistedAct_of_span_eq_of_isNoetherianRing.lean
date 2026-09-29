-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e443778b-2c2a-5d7f-8c0d-93ab46d6a72d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_bijective_and_isBaseChange_and_isPullback_omegaObj_of_isZariskiSheaf_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal
import Theorems.Thm_CerednikDrinfeld_exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_exists_equiv_of_ringEquiv_frame
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀ CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv CerednikDrinfeld.GradedCartierModuleData.module CerednikDrinfeld.GradedCartierModuleData.addCommGroup CerednikDrinfeld.GradedCartierModuleData.instModuleWittVectorSigma"
p2m_attr_erase "instance" "CerednikDrinfeld.GradedCartierModuleData.instAddCommGroupSigma MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector MvFormalGroup.instIsCommMapRingHom MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType MvFormalGroup.CartierModule.instModulePadicInt CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup HopfAlgebra.HopfIdealQuotient.instIsCocomm"
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply"
p2m_attr_erase "simp" "CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_verschiebungInt MvFormalGroup.WittLaw.xTaut_coeff MvFormalGroup.WittLaw.frobPolyFam_apply MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"
p2m_attr_erase "simp" "CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one CerednikDrinfeld.FormalOmega.AlgFunctor.algHomOfComp_apply CerednikDrinfeld.FormalOmega.AlgFunctor.toModuliPackage_obj AlgebraicGeometry.Scheme.nilpPoints_map_val CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst CerednikDrinfeld.FormalODModule.frobTwist_F CerednikDrinfeld.FormalODModule.frobTwist_frobTwist CerednikDrinfeld.FormalODModule.frobTwist_varpi CerednikDrinfeld.FormalODModule.frobTwist_act"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

namespace Blk407D

theorem units_algebraMap_zpow {R S : Type} [CommRing R] [Field S] [Algebra R S] (x : Rˣ) (m : ℤ) :
    algebraMap R S ((x ^ m : Rˣ) : R) = (algebraMap R S (x : R)) ^ m := by
  have h : Units.map (algebraMap R S : R →* S) (x ^ m) = Units.map (algebraMap R S : R →* S) x ^ m := map_zpow _ _ _
  calc algebraMap R S ((x ^ m : Rˣ) : R) = ((Units.map (algebraMap R S : R →* S) (x ^ m) : Sˣ) : S) := rfl
    _ = ((Units.map (algebraMap R S : R →* S) x ^ m : Sˣ) : S) := by rw [h]
    _ = ((Units.map (algebraMap R S : R →* S) x : Sˣ) : S) ^ m := Units.val_zpow_eq_zpow_val _ _
    _ = (algebraMap R S (x : R)) ^ m := rfl

theorem units_algebraMap_zpow_inv_mul {R S : Type} [CommRing R] [Field S] [Algebra R S] (x : Rˣ) (m : ℤ) :
    algebraMap R S (((x ^ m)⁻¹ : Rˣ) : R) * (algebraMap R S (x : R)) ^ m = 1 := by
  rw [← units_algebraMap_zpow, ← map_mul, Units.inv_mul, map_one]

theorem vdet_law_transport {r : ℕ} [Fact r.Prime]
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    (e𝒪 : ℤ_[r] ≃+* 𝒪) (eK : ℚ_[r] ≃+* K₀)
    (hcomm' : ∀ x : ℤ_[r], eK (algebraMap ℤ_[r] ℚ_[r] x) = algebraMap 𝒪 K₀ (e𝒪 x))
    (π : 𝒪) (w : 𝒪ˣ) (hw : e𝒪 ((r : ℕ) : ℤ_[r]) * ↑w = π)
    (d : ℚ_[r]) (n : ℤ) :
    (∃ u : 𝒪ˣ, eK d = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n) ↔
      ∃ u : ℤ_[r]ˣ, d = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n := by
  have heKu : ∀ y : 𝒪, eK.symm (algebraMap 𝒪 K₀ y) = algebraMap ℤ_[r] ℚ_[r] (e𝒪.symm y) := by
    intro y
    apply eK.injective
    rw [RingEquiv.apply_symm_apply, hcomm', RingEquiv.apply_symm_apply]
  have hπ' : e𝒪.symm π = ((r : ℕ) : ℤ_[r]) * ↑(Units.map (e𝒪.symm : 𝒪 ≃+* ℤ_[r]).toRingHom.toMonoidHom w) := by
    rw [← hw, map_mul, RingEquiv.symm_apply_apply, Units.coe_map]; rfl
  have hπK : algebraMap 𝒪 K₀ π = algebraMap 𝒪 K₀ (e𝒪 ((r : ℕ) : ℤ_[r])) * algebraMap 𝒪 K₀ (w : 𝒪) := by
    rw [← map_mul, hw]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Units.map (e𝒪.symm : 𝒪 ≃+* ℤ_[r]).toRingHom.toMonoidHom u *
      Units.map (e𝒪.symm : 𝒪 ≃+* ℤ_[r]).toRingHom.toMonoidHom w ^ n, ?_⟩
    have hu' := congrArg eK.symm hu
    rw [RingEquiv.symm_apply_apply, map_mul, map_zpow₀, heKu, heKu, hπ'] at hu'
    rw [hu', Units.val_mul, map_mul, map_mul, units_algebraMap_zpow, Units.coe_map, mul_zpow]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Units.coe_map]
    ring
  · rintro ⟨u₀, hu₀⟩
    refine ⟨Units.map (e𝒪 : ℤ_[r] ≃+* 𝒪).toRingHom.toMonoidHom u₀ * (w ^ n)⁻¹, ?_⟩
    have h1 := units_algebraMap_zpow_inv_mul (S := K₀) w n
    rw [hu₀, map_mul, map_zpow₀, hcomm', hcomm', hπK, Units.val_mul, map_mul, mul_zpow, Units.coe_map]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    linear_combination (-(algebraMap 𝒪 K₀ (e𝒪 (u₀ : ℤ_[r])) * (algebraMap 𝒪 K₀ (e𝒪 ((r : ℕ) : ℤ_[r]))) ^ n)) * h1

end Blk407D

theorem solution
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)
    :
    ∃ (ι : Zp2 r →+* Onr)
      (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
      (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
      (_ : Φ.HasHeight 4)
      (M : ModuliPackage.{0, 0} r Onr) (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
        Rigidified r Φ B → M.obj B ψ hB)
      (_ : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
            (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
            (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
        (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
            (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
            (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
            η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
            ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
              ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
                (hL : IsNilpotent (r : L)),
                ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                  η L ((algebraMap B L).comp ψ) hL t =
                    M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 M).obj B), e B' hB' ((ModuliPackage.G 𝒪 M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist Onr Fr 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 M).obj B), ∃ x' : (ModuliPackage.G 𝒪 M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') := by
  classical

  obtain ⟨k, hk₁, hk₂, hk₃, eW, q, heW, -, -, -⟩ :=
    CerednikDrinfeld.exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal r Onr (algebraMap 𝒪 Onr π)
      (by
        have h := congrArg (Ideal.map (algebraMap 𝒪 Onr)) hunr
        simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h.symm)
      hOnr_complete hOnr_max hOnr_closed (Fr : Onr ≃+* Onr) hFr
  letI : Field k := hk₁
  haveI : CharP k r := hk₂
  haveI : IsAlgClosed k := hk₃
  obtain ⟨e𝒪, eK, he𝒪⟩ :=
    CerednikDrinfeld.exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq r 𝒪 hdvr π hπ hcomplete hres hunr K₀

  letI instAlgW : Algebra ℤ_[r] (WittVector r k) :=
    ((eW.symm : Onr ≃+* WittVector r k).toRingHom.comp ((algebraMap 𝒪 Onr).comp (e𝒪 : ℤ_[r] ≃+* 𝒪).toRingHom)).toAlgebra
  have halg : ∀ x : ℤ_[r], algebraMap ℤ_[r] (WittVector r k) x = eW.symm (algebraMap 𝒪 Onr (e𝒪 x)) := fun x => rfl
  have heO : ∀ x : ℤ_[r], eW (algebraMap ℤ_[r] (WittVector r k) x) = algebraMap 𝒪 Onr (e𝒪 x) := by
    intro x; rw [halg]; exact eW.apply_symm_apply _
  let FrW : WittVector r k ≃+* WittVector r k := eW.trans ((Fr : Onr ≃+* Onr).trans eW.symm)
  have hFrW : ∀ x, FrW x = WittVector.frobenius x := by
    intro x
    calc FrW x = eW.symm ((Fr : Onr ≃+* Onr) (eW x)) := rfl
      _ = eW.symm (eW (WittVector.frobenius x)) := by rw [← heW]
      _ = WittVector.frobenius x := eW.symm_apply_apply _
  have hFrW_alg : ∀ x : ℤ_[r], FrW (algebraMap ℤ_[r] (WittVector r k) x) = algebraMap ℤ_[r] (WittVector r k) x := by
    intro x
    calc FrW (algebraMap ℤ_[r] (WittVector r k) x) = eW.symm ((Fr : Onr ≃+* Onr) (eW (algebraMap ℤ_[r] (WittVector r k) x))) := rfl
      _ = eW.symm ((Fr : Onr ≃+* Onr) (algebraMap 𝒪 Onr (e𝒪 x))) := by rw [heO]
      _ = eW.symm (algebraMap 𝒪 Onr (e𝒪 x)) := by rw [show (Fr : Onr ≃+* Onr) (algebraMap 𝒪 Onr (e𝒪 x)) = Fr (algebraMap 𝒪 Onr (e𝒪 x)) from rfl, AlgEquiv.commutes]
      _ = algebraMap ℤ_[r] (WittVector r k) x := (halg x).symm
  let Fr₀ : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k := AlgEquiv.ofRingEquiv (f := FrW) hFrW_alg
  have hFr₀ : ∀ x : WittVector r k, Fr₀ x = WittVector.frobenius x := fun x => hFrW x
  have hFr' : ∀ y, eW (Fr₀ y) = Fr (eW y) := by intro y; rw [hFr₀, heW]; rfl
  have hcomm' : ∀ x : ℤ_[r], eK (algebraMap ℤ_[r] ℚ_[r] x) = algebraMap 𝒪 K₀ (e𝒪 x) := by
    intro x; rw [he𝒪]; rfl
  let vdet₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ :=
    vdet.comp (Matrix.GeneralLinearGroup.map (eK : ℚ_[r] ≃+* K₀).toRingHom)
  have hv' : ∀ g, vdet (Matrix.GeneralLinearGroup.map (eK : ℚ_[r] ≃+* K₀).toRingHom g) = vdet₀ g := fun g => rfl

  have hspan : Ideal.span {e𝒪 ((r : ℕ) : ℤ_[r])} = Ideal.span {π} := by rw [map_natCast]; exact hunr
  obtain ⟨w, hw⟩ : Associated (e𝒪 ((r : ℕ) : ℤ_[r])) π := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hdet : ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r],
      ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (eK : ℚ_[r] ≃+* K₀).toRingHom g) : K₀ˣ) : K₀) =
        eK ((Matrix.GeneralLinearGroup.det g : ℚ_[r]ˣ) : ℚ_[r]) := by
    intro g
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (eK : ℚ_[r] ≃+* K₀).toRingHom (g : Matrix (Fin 2) (Fin 2) ℚ_[r])).symm
  have hvdet₀ : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet₀ g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) =
        algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n := by
    intro g n
    rw [← hv', hvdet, hdet]
    exact Blk407D.vdet_law_transport e𝒪 eK hcomm' π w hw _ n

  obtain ⟨ι, Φ, hΦ, hΦ4, M, hM, η, hη₁, hη₂, hη₃⟩ :=
    CerednikDrinfeld.SpecialFormal.exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing r k

  have hη : _ ∧ _ ∧ _ := ⟨hη₁, fun (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B]
    [IsNoetherianRing B'] => hη₂ B B', hη₃⟩
  clear hη₁ hη₂ hη₃
  have hmaster :=
    CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_bijective_and_isBaseChange_and_isPullback_omegaObj_of_isZariskiSheaf_of_isNoetherianRing r k ι Φ hΦ hΦ4 M hM η hη
  obtain ⟨E₀, hE₀, e, he⟩ :=
    CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing k Fr₀ hFr₀ vdet₀ hvdet₀ ι Φ hΦ hΦ4 M hM η hη hmaster

  have hΨ :=
    CerednikDrinfeld.FormalOmega.OmegaNr.exists_equiv_of_ringEquiv_frame
      (𝒪 := ℤ_[r]) (K := ℚ_[r]) (𝒪' := 𝒪) (K' := K₀) e𝒪 eK hcomm' (π := ((r : ℕ) : ℤ_[r])) (π' := e𝒪 ((r : ℕ) : ℤ_[r])) rfl
      (WittVector r k) Fr₀ vdet₀ Onr Fr vdet eW heO hFr' hv'
  have hΞ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_equiv_of_span_singleton_eq
      (𝒪 := 𝒪) (K := K₀) (π := e𝒪 ((r : ℕ) : ℤ_[r])) (π₂ := π) hspan
  exact CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
    ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr₀ vdet₀ 𝒪 K₀ π Onr Fr vdet
    e𝒪 eK hcomm' (e𝒪 ((r : ℕ) : ℤ_[r])) rfl hspan eW heO hFr' hv' hΨ hΞ
    ⟨ι, Φ, hΦ, hΦ4, M, hM, η, hη, E₀, hE₀, e, he⟩

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing (solution)
