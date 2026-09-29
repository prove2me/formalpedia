-- Prove2me | solution 1 for CerednikDrinfeld.exists_ringEquiv_functionField_pullback_invariantFieldOf_smul_level_of_cerednikDrinfeld_quotient_of_tame_of_virtuallyTorsionFree_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/43073f50-0c8f-5620-8717-be2bf38b72e5

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_exists_adicPoint_to_sections_of_cerednikDrinfeld_quotient
import Theorems.Thm_CerednikDrinfeld_FormalOmega_isAdicFrame_of_injective_of_forall_le_one_iff_mem_range
import Theorems.Thm_CerednikDrinfeld_isIntegral_pullback_of_cerednikDrinfeld_quotient_of_smooth
import Theorems.Thm_CerednikDrinfeld_exists_ringHom_functionField_invariantFieldOf_eval_of_cerednikDrinfeld_quotient_of_smooth
import Theorems.Thm_CerednikDrinfeld_surjective_ringHom_functionField_invariantFieldOf_of_eval_of_tame_of_cerednikDrinfeld_quotient_of_virtuallyTorsionFree_of_smooth
import Theorems.Thm_CerednikDrinfeld_finite_affinoid_toOmega_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth
import Theorems.Thm_CerednikDrinfeld_ringHom_functionField_germ_app_eq_inv_smul_of_eval_of_cerednikDrinfeld_quotient
import Theorems.Thm_CerednikDrinfeld_ringHom_functionField_germ_app_eq_inv_smul_of_frobenius_of_eval_of_cerednikDrinfeld_quotient
import Theorems.Thm_CerednikDrinfeld_ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ringEquiv_functionField_pullback_invariantFieldOf_smul_level_of_cerednikDrinfeld_quotient_of_tame_of_virtuallyTorsionFree_of_smooth
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀ AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqV AlgebraicCurve.TotallyDegenerateCovering.instFintypeV AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqE AlgebraicCurve.TotallyDegenerateCovering.instFintypeE instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_b AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_w AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_a AlgebraicCurve.TotallyDegenerateCovering.mk.sizeOf_spec AlgebraicCurve.TotallyDegenerateCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

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

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))

    (hvtf : ∃ Γ'' : Subgroup G, Γ'' ≤ Γ' ∧ Γ''.relIndex Γ' ≠ 0 ∧ ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1)
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪)) [IsProper f] [Flat f]

    (hsmooth : SmoothOfRelativeDimension 1 (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀)))))
    (hgconn : GeometricallyConnected (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀)))))

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ P : (Omega K₀ π).obj k, Θ k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
        ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)

    (ι : Type) (𝒴 : ι → Scheme.{0}) (fY : ∀ i : ι, 𝒴 i ⟶ Spec (CommRingCat.of 𝒪)) [∀ i : ι, IsProper (fY i)] [∀ i : ι, Flat (fY i)]

    (hsmoothY : ∀ i : ι, SmoothOfRelativeDimension 1 (Limits.pullback.snd (fY i) (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀)))))
    (hgconnY : ∀ i : ι, GeometricallyConnected (Limits.pullback.snd (fY i) (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀)))))
    (ΓY : ι → Subgroup G)
    (hcentY : ∀ i : ι, ∃ z ∈ ΓY i, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hoddY : ∀ i : ι, ∃ w ∈ ΓY i, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (ΓY' : ι → Subgroup G) (hΓY' : ∀ (i : ι) (x : G), x ∈ ΓY' i ↔ x ∈ ΓY i ∧ Even (Multiplicative.toAdd (vdet (σ x))))
    (hdiscY : ∀ (i : ι) (v : LT.LatticeTree.Vertex 𝒪 K₀), Set.Finite {g : PGL(2, K₀) | g ∈ (ΓY' i).map ρ ∧ g • v = v})
    (hcocptY : ∀ i : ι, ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ (ΓY' i).map ρ, g • v ∈ S)
    (ΘY : ∀ (i : ι) (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints (fY i)).obj B)
    (hΘYnat : ∀ (i : ι) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ΘY i B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints (fY i)).map φ (ΘY i B hB x))
    (hΘYinv : ∀ (i : ι) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ ΓY i →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ΘY i B hB x' = ΘY i B hB x)
    (hΘYfib : ∀ (i : ι) (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints (fY i)).obj k, ∃ P : (Omega K₀ π).obj k, ΘY i k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, ΘY i k hk (ψ, P) = ΘY i k hk (ψ, P') ↔
        ∃ γ ∈ ΓY i, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (hΘYuniv : ∀ (i : ι) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ ΓY i →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints (fY i)).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints (fY i)).obj B),
          u B' hB' ((Scheme.nilpPoints (fY i)).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (ΘY i B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints (fY i)).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints (fY i)).obj B),
            u' B' hB' ((Scheme.nilpPoints (fY i)).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (ΘY i B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints (fY i)).obj B),
            u' B hB y = u B hB y)

    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε)

    (htame : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀,
      Valued.v ((Nat.card ↥{g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v} : ℕ) : C) = 1)
    (htameY : ∀ (i : ι) (v : LT.LatticeTree.Vertex 𝒪 K₀),
      Valued.v ((Nat.card ↥{g : PGL(2, K₀) | g ∈ (ΓY' i).map ρ ∧ g • v = v} : ℕ) : C) = 1)
    (hvtfY : ∀ i : ι, ∃ Γ'' : Subgroup G, Γ'' ≤ ΓY' i ∧ Γ''.relIndex (ΓY' i) ≠ 0 ∧ ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1)
    [CompleteSpace C] [IsAlgClosed C]
    (h𝒪 : ∀ x : K₀, x ∈ Set.range (algebraMap 𝒪 K₀) ↔ Valued.v (algebraMap K₀ C x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ C) (hϖ : algebraMap 𝒪 K₀ π = ϖ.ϖ) (hex : Omega.IsExhausted ϖ)
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    (ψ₀ : Onr →+* C) (hψ₀ : ∀ y : Onr, Valued.v (ψ₀ y) ≤ 1)
    (hψ₀𝒪 : ψ₀.comp (algebraMap 𝒪 Onr) = (algebraMap K₀ C).comp (algebraMap 𝒪 K₀))

    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪))
    (hsC : sC = Spec.map (CommRingCat.ofHom ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀)))) :
    ∃ _ : IsIntegral (Limits.pullback f sC),
    ∃ e : ↑(Limits.pullback f sC).functionField ≃+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'),

      (∀ c : C, e (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC) c) =
        algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') c) ∧

      (∀ (a : 𝒳 ⟶ 𝒳) (haf : a ≫ f = f) (g : G), vdet (σ g) = 1 →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
            OmegaNr.IsTwistedAct π Onr Fr vdet B (σ g) x x' → (Scheme.nilpPoints.mapHom f f a haf).app B (Θ B hB x) = Θ B hB x') →
        ∀ (aC : Limits.pullback f sC ⟶ Limits.pullback f sC),
          aC ≫ Limits.pullback.fst f sC = Limits.pullback.fst f sC ≫ a → aC ≫ Limits.pullback.snd f sC = Limits.pullback.snd f sC →
        ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ aC ⁻¹ᵁ U) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f sC).presheaf.germ (aC ⁻¹ᵁ U) (genericPoint (Limits.pullback f sC : Scheme.{0})) hU').hom ((aC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
            g⁻¹ • ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ))) ∧

      (∀ (b : 𝒳 ⟶ 𝒳) (hbf : b ≫ f = f),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
            (Scheme.nilpPoints.mapHom f f b hbf).app B (Θ B hB x) = Θ B hB (frobTwist Onr Fr 1 x.1, x.2)) →
        ∀ (bC : Limits.pullback f sC ⟶ Limits.pullback f sC),
          bC ≫ Limits.pullback.fst f sC = Limits.pullback.fst f sC ≫ b → bC ≫ Limits.pullback.snd f sC = Limits.pullback.snd f sC →
        ∀ (w : G), w ∈ Γ → vdet (σ w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ bC ⁻¹ᵁ U) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f sC).presheaf.germ (bC ⁻¹ᵁ U) (genericPoint (Limits.pullback f sC : Scheme.{0})) hU').hom ((bC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
            w⁻¹ • ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ))) ∧

      (∀ (s : Omega.IsometricAut K₀ C) (n : ℤ),
        (∀ y : Onr, Fr (Fr y) = y → s.toRingEquiv (ψ₀ y) = ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y)) →
        ∀ (tC : Limits.pullback f sC ⟶ Limits.pullback f sC),
          tC ≫ Limits.pullback.fst f sC = Limits.pullback.fst f sC →
          tC ≫ Limits.pullback.snd f sC = Limits.pullback.snd f sC ≫ Spec.map (CommRingCat.ofHom (s.toRingEquiv : C →+* C)) →
        ∀ (w : G), w ∈ Γ → vdet (σ w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f sC).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint (Limits.pullback f sC : Scheme.{0})) hU').hom ((tC.app U).hom sec)) :
              ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
            w ^ n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ s)
              ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom sec) :
                ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ))) ∧

      (∀ i : ι, ∃ _ : IsIntegral (Limits.pullback (fY i) sC),
        ∃ eY : ↑(Limits.pullback (fY i) sC).functionField ≃+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) (ΓY' i)),
          (∀ c : C, eY (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd (fY i) sC) c) =
            algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) (ΓY' i)) c) ∧
          (∀ (h : 𝒴 i ⟶ 𝒳) (hhf : h ≫ f = fY i) (g : G), vdet (σ g) = 1 →
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
                (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
                OmegaNr.IsTwistedAct π Onr Fr vdet B (σ g) x x' →
                  (Scheme.nilpPoints.mapHom (fY i) f h hhf).app B (ΘY i B hB x) = Θ B hB x') →
            ∀ (hC : Limits.pullback (fY i) sC ⟶ Limits.pullback f sC),
              hC ≫ Limits.pullback.fst f sC = Limits.pullback.fst (fY i) sC ≫ h →
              hC ≫ Limits.pullback.snd f sC = Limits.pullback.snd (fY i) sC →
            ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
              (hU' : genericPoint (Limits.pullback (fY i) sC : Scheme.{0}) ∈ hC ⁻¹ᵁ U)
              (sec : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
              ((eY (((Limits.pullback (fY i) sC).presheaf.germ (hC ⁻¹ᵁ U) (genericPoint (Limits.pullback (fY i) sC : Scheme.{0})) hU').hom
                  ((hC.app U).hom sec)) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) (ΓY' i))) : FractionRing (Omega.HolRingOf ϖ ρ)) =
                g⁻¹ • ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom sec) :
                  ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)))) := by
  classical

  letI instAlgOC : Algebra 𝒪 C := ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀)).toAlgebra
  haveI instTowOKC : IsScalarTower 𝒪 K₀ C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let Rv : ValuationSubring C := (Valued.v (R := C)).valuationSubring
  have hmemRv : ∀ c : C, c ∈ Rv ↔ Valued.v c ≤ 1 := fun c => Valuation.mem_valuationSubring_iff _ _
  have hOC : ∀ a : 𝒪, algebraMap 𝒪 C a ∈ Rv := fun a =>
    (hmemRv _).2 ((h𝒪 (algebraMap 𝒪 K₀ a)).1 ⟨a, rfl⟩)
  letI instAlgOR : Algebra 𝒪 Rv := ((algebraMap 𝒪 C).codRestrict Rv hOC).toAlgebra
  haveI instTowORC : IsScalarTower 𝒪 Rv C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hF : IsAdicFrame π ϖ Rv :=
    CerednikDrinfeld.FormalOmega.isAdicFrame_of_injective_of_forall_le_one_iff_mem_range π hπ hcomplete K₀ C hrk h𝒪 ϖ hϖ Rv
      Subtype.val_injective
      (fun c => ⟨fun hc => ⟨⟨c, (hmemRv c).2 hc⟩, rfl⟩, fun hc => by obtain ⟨y, rfl⟩ := hc; exact (hmemRv _).1 y.2⟩)
  let ψ₀R : Onr →ₐ[𝒪] Rv :=
    { toRingHom := ψ₀.codRestrict Rv (fun y => (hmemRv _).2 (hψ₀ y))
      commutes' := fun a => Subtype.ext (RingHom.congr_fun hψ₀𝒪 a) }

  obtain ⟨Φ, hΦ⟩ := CerednikDrinfeld.exists_adicPoint_to_sections_of_cerednikDrinfeld_quotient
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv ϖ hF ψ₀R

  haveI hint : IsIntegral (Limits.pullback f sC) :=
    CerednikDrinfeld.isIntegral_pullback_of_cerednikDrinfeld_quotient_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f hsmooth hgconn Θ hΘnat hΘinv hΘfib hΘuniv C hrk h𝒪 ϖ hϖ hex ψ₀ hψ₀ hψ₀𝒪 sC hsC

  obtain ⟨e, he₀, hev⟩ := CerednikDrinfeld.exists_ringHom_functionField_invariantFieldOf_eval_of_cerednikDrinfeld_quotient_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f hsmooth Θ hΘnat hΘinv hΘfib hΘuniv ϖ hF ψ₀R hrk hval hex Φ hΦ sC hsC
  have hsurj : Function.Surjective e :=
    CerednikDrinfeld.surjective_ringHom_functionField_invariantFieldOf_of_eval_of_tame_of_cerednikDrinfeld_quotient_of_virtuallyTorsionFree_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hvtf hdisc hcocpt 𝒳 f hsmooth Θ hΘnat hΘinv hΘfib hΘuniv ϖ hF ψ₀R hrk hval htame hex Φ hΦ sC hsC e he₀ hev
  let eE : ↑(Limits.pullback f sC).functionField ≃+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') :=
    RingEquiv.ofBijective e ⟨e.injective, hsurj⟩
  have heE₀ : ∀ c : C, eE (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC) c) =
      algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') c := fun c => he₀ c

  have hfin := CerednikDrinfeld.finite_affinoid_toOmega_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f hsmooth Θ hΘnat hΘinv hΘfib hΘuniv ϖ hF ψ₀R hrk hval hex Φ hΦ sC hsC eE heE₀
  refine ⟨hint, eE, heE₀, ?_, ?_, ?_, ?_⟩
  ·
    intro a haf g hg ha aC h1 h2 U hU hU' s
    exact CerednikDrinfeld.ringHom_functionField_germ_app_eq_inv_smul_of_eval_of_cerednikDrinfeld_quotient
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv 𝒳 f Γ' Θ hΘnat ϖ hF ψ₀R hrk hval hex Φ hΦ Φ hΦ sC hsC e hev e hev hfin hfin a haf g hg ha aC h1 h2 U hU hU' s
  ·
    intro b hbf hb bC h1 h2 w hw hw1 U hU hU' s
    exact CerednikDrinfeld.ringHom_functionField_germ_app_eq_inv_smul_of_frobenius_of_eval_of_cerednikDrinfeld_quotient
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv ϖ hF ψ₀R hrk hval hex Φ hΦ sC hsC e hev hfin b hbf hb bC h1 h2 w hw hw1 U hU hU' s
  ·
    intro s n hs tC h1 h2 w hw hw1 U hU hU' sec
    exact CerednikDrinfeld.ringHom_functionField_germ_app_eq_zpow_smul_fracMap_of_isometricAut_of_eval_of_cerednikDrinfeld_quotient
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv ϖ hF ψ₀R hrk hval hex Φ hΦ sC hsC e hev hfin s n (fun y hy => hs y hy) tC h1 h2 w hw hw1 U hU hU' sec
  ·
    intro i
    obtain ⟨ΦY, hΦY⟩ := CerednikDrinfeld.exists_adicPoint_to_sections_of_cerednikDrinfeld_quotient
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ (ΓY i) (hcentY i)
        (hoddY i) (ΓY' i) (hΓY' i) ρ hρ (hdiscY i) (hcocptY i) (𝒴 i) (fY i) (ΘY i) (hΘYnat i) (hΘYinv i) (hΘYfib i) (hΘYuniv i) ϖ hF ψ₀R
    haveI hintY : IsIntegral (Limits.pullback (fY i) sC) :=
      CerednikDrinfeld.isIntegral_pullback_of_cerednikDrinfeld_quotient_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ (ΓY i) (hcentY i)
        (hoddY i) (ΓY' i) (hΓY' i) ρ hρ (hdiscY i) (hcocptY i) (𝒴 i) (fY i) (hsmoothY i) (hgconnY i) (ΘY i) (hΘYnat i) (hΘYinv i) (hΘYfib i) (hΘYuniv i) C hrk h𝒪 ϖ hϖ hex ψ₀ hψ₀ hψ₀𝒪 sC hsC
    obtain ⟨eY, heY₀, heYv⟩ := CerednikDrinfeld.exists_ringHom_functionField_invariantFieldOf_eval_of_cerednikDrinfeld_quotient_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ (ΓY i) (hcentY i)
        (hoddY i) (ΓY' i) (hΓY' i) ρ hρ (hdiscY i) (hcocptY i) (𝒴 i) (fY i) (hsmoothY i) (ΘY i) (hΘYnat i) (hΘYinv i) (hΘYfib i) (hΘYuniv i) ϖ hF ψ₀R hrk hval hex ΦY hΦY sC hsC
    have hsurjY : Function.Surjective eY :=
      CerednikDrinfeld.surjective_ringHom_functionField_invariantFieldOf_of_eval_of_tame_of_cerednikDrinfeld_quotient_of_virtuallyTorsionFree_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ (ΓY i) (hcentY i)
        (hoddY i) (ΓY' i) (hΓY' i) ρ hρ (hvtfY i) (hdiscY i) (hcocptY i) (𝒴 i) (fY i) (hsmoothY i) (ΘY i) (hΘYnat i) (hΘYinv i) (hΘYfib i) (hΘYuniv i) ϖ hF ψ₀R hrk hval (htameY i) hex ΦY hΦY sC hsC eY heY₀ heYv
    let eYE : ↑(Limits.pullback (fY i) sC).functionField ≃+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) (ΓY' i)) :=
      RingEquiv.ofBijective eY ⟨eY.injective, hsurjY⟩
    have heYE₀ : ∀ c : C, eYE (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd (fY i) sC) c) =
        algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) (ΓY' i)) c := fun c => heY₀ c
    have hfinY := CerednikDrinfeld.finite_affinoid_toOmega_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ (ΓY i) (hcentY i)
        (hoddY i) (ΓY' i) (hΓY' i) ρ hρ (hdiscY i) (hcocptY i) (𝒴 i) (fY i) (hsmoothY i) (ΘY i) (hΘYnat i) (hΘYinv i) (hΘYfib i) (hΘYuniv i) ϖ hF ψ₀R hrk hval hex ΦY hΦY sC hsC eYE heYE₀
    refine ⟨hintY, eYE, heYE₀, ?_⟩
    intro h hhf g hg hh hC h1 h2 U hU hU' sec
    exact CerednikDrinfeld.ringHom_functionField_germ_app_eq_inv_smul_of_eval_of_cerednikDrinfeld_quotient
        𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
        Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv (𝒴 i) (fY i) (ΓY' i) (ΘY i) (hΘYnat i) ϖ hF ψ₀R hrk hval hex Φ hΦ ΦY hΦY sC hsC e hev eY heYv hfin hfinY
        h hhf g hg hh hC h1 h2 U hU hU' sec

end S_CerednikDrinfeld_exists_ringEquiv_functionField_pullback_invariantFieldOf_smul_level_of_cerednikDrinfeld_quotient_of_tame_of_virtuallyTorsionFree_of_smooth
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ringEquiv_functionField_pullback_invariantFieldOf_smul_level_of_cerednikDrinfeld_quotient_of_tame_of_virtuallyTorsionFree_of_smooth (solution)
