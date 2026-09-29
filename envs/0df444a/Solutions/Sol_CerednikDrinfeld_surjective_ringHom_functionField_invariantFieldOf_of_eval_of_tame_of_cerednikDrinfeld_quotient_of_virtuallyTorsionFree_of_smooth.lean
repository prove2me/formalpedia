-- Prove2me | solution 1 for CerednikDrinfeld.surjective_ringHom_functionField_invariantFieldOf_of_eval_of_tame_of_cerednikDrinfeld_quotient_of_virtuallyTorsionFree_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b46ea444-287e-572a-b452-128d34e33eab

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_Omega_isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range
import Theorems.Thm_AlgebraicCurve_isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem
import Theorems.Thm_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving
import Theorems.Thm_CerednikDrinfeld_Omega_surjective_place_invariantFieldOf_of_mem_iff_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le
import Theorems.Thm_CerednikDrinfeld_Omega_place_invariantFieldOf_eq_iff_exists_eq_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
import Theorems.Thm_AlgebraicCurve_surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finite_intermediateField_of_transcendental_mem
import Theorems.Thm_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated
import Theorems.Thm_CerednikDrinfeld_BruhatTits_treeLattice_facts_map_evenPart
import Theorems.Thm_CerednikDrinfeld_map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
import Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField
import Theorems.Thm_CerednikDrinfeld_finite_affinoid_toOmega_of_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth
import Theorems.Thm_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset
import Theorems.Thm_CerednikDrinfeld_exists_invariant_chartwiseMeromorphic_pullback_of_cerednikDrinfeld_quotient_of_eval_of_smooth
import Theorems.Thm_CerednikDrinfeld_exists_functionField_ne_const_of_cerednikDrinfeld_quotient
import Theorems.Thm_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_injective
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_surjective_ringHom_functionField_invariantFieldOf_of_eval_of_tame_of_cerednikDrinfeld_quotient_of_virtuallyTorsionFree_of_smooth
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega~stalk CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve"

noncomputable section

namespace ESURJ

noncomputable def specValue {R : Type} [CommRing R] {X : Scheme.{0}} (P : Spec (CommRingCat.of R) ⟶ X) (V : X.Opens)
    (p : X.presheaf.obj (Opposite.op V)) (hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ V) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hV).op).hom ((P.app V).hom p))

theorem specValue_eq_zero_iff_germ_mem_maximalIdeal {C : Type} [Field C] {X : Scheme.{0}}
    (q : Spec (CommRingCat.of C) ⟶ X) (U : X.Opens) (s : X.presheaf.obj (Opposite.op U))
    (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U) (pt : Spec (CommRingCat.of C)) :
    specValue q U s hqU = 0 ↔
      (X.presheaf.germ U (q.base pt) (hqU (Set.mem_univ pt))).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (q.base pt)) := by
  classical
  set t : (Spec (CommRingCat.of C)).presheaf.obj (Opposite.op ⊤) :=
    ((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s) with ht
  set c : C := (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom t with hc
  have hspec : specValue q U s hqU = c := rfl

  have htc : t = (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c := by
    rw [hc, ← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl

  have hgerm : (q.stalkMap pt).hom ((X.presheaf.germ U (q.base pt) (hqU (Set.mem_univ pt))).hom s) =
      ((Spec (CommRingCat.of C)).presheaf.germ ⊤ pt (Set.mem_univ pt)).hom t := by
    rw [Scheme.Hom.germ_stalkMap_apply, ht]
    exact ((Spec (CommRingCat.of C)).presheaf.germ_res_apply (homOfLE hqU) pt (Set.mem_univ pt) _).symm

  have hgerm' : ((Spec (CommRingCat.of C)).presheaf.germ ⊤ pt (Set.mem_univ pt)).hom t =
      (StructureSheaf.toStalk C pt).hom c := by
    rw [htc]
    show ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (Spec (CommRingCat.of C)).presheaf.germ ⊤ pt (Set.mem_univ pt)).hom c = _
    have h2 := StructureSheaf.toOpen_germ (R := C) ⊤ pt (Set.mem_univ pt)
    rw [Scheme.ΓSpecIso_inv]
    exact congrArg (fun φ => CommRingCat.Hom.hom φ c) h2
  have key : IsUnit ((StructureSheaf.toStalk C pt).hom c) ↔ c ∉ pt.asIdeal :=
    IsLocalization.AtPrime.isUnit_to_map_iff (↑((Spec.structureSheaf C).presheaf.stalk pt)) pt.asIdeal c

  haveI : IsLocalHom (q.stalkMap pt).hom := LocallyRingedSpace.Hom.prop q.toLRSHom pt
  rw [hspec, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (q.stalkMap pt).hom, hgerm, hgerm']
  have hbot : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime pt.asIdeal
  constructor
  · intro h0 hu
    have h1 := key.1 hu
    rw [hbot, h0] at h1
    exact h1 (Ideal.zero_mem ⊥)
  · intro hnu
    by_contra h0
    apply hnu
    exact key.2 (by rw [hbot, Ideal.mem_bot]; exact h0)

end ESURJ

namespace ESURJ

theorem mem_place_and_evalAt_eq_of_local_quotient
    (K₀ : Type) [Field K₀] (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace C] [IsAlgClosed C]
    (ϖ : Omega.PseudoUniformizer K₀ C) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ C a - algebraMap K₀ C t) < (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)] (Γ : Subgroup G)
    (FC : Type) [Field FC] [Algebra C FC]
    (eFC : FC ≃ₐ[C] ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ))
    (pt : ↥(Omega.upperHalfPlane K₀ C) → Place C FC)
    (hpt1 : ∀ (z : ↥(Omega.upperHalfPlane K₀ C)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ C) → C) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩)
    (hpt2 : ∀ (z : ↥(Omega.upperHalfPlane K₀ C)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ C) → C) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ C) → C) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ C) → C) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ C) → C) z = 0))

    (x : FC) (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
    (hxab : ((eFC x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk a ⟨b, hb⟩)

    (z : ↥(Omega.upperHalfPlane K₀ C)) (N : ℕ) (hD : {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ⊆ Omega.upperHalfPlane K₀ C)
    (a' b' : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} → C) (ha' : a' ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}) (hb' : b' ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N})
    (hbz : ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, (w : C) = (z : C) → b' w ≠ 0)
    (Fv : ↥(Omega.upperHalfPlane K₀ C) → C)
    (hloc : ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, b' w * Fv ⟨(w : C), hD w.2⟩ = a' w)
    (hval : ∃ Z : Set ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, Z.Finite ∧ ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, w ∉ Z →
      (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(w : C), hD w.2⟩ * Fv ⟨(w : C), hD w.2⟩ = (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(w : C), hD w.2⟩) :
    x ∈ (pt z).toValuationSubring ∧ (pt z).evalAt x = Fv z ∧ (x ∈ (pt z).toValuationSubring.nonunits ↔ Fv z = 0) := by
  classical
  have hz0 : (z : C) ∈ {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} := by
    show Valued.v ((z : C) - (z : C)) ≤ _
    rw [sub_self, map_zero]; exact zero_le'
  set z₀ : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} := ⟨(z : C), hz0⟩ with hz₀
  have hzz : (⟨(z₀ : C), hD z₀.2⟩ : ↥(Omega.upperHalfPlane K₀ C)) = z := Subtype.ext rfl

  obtain ⟨Z, hZ, hvalZ⟩ := hval
  have heq : ∃ Z : Set ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, Z.Finite ∧ ∀ w, w ∉ Z →
      (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(w : C), hD w.2⟩ * a' w = (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(w : C), hD w.2⟩ * b' w := by
    refine ⟨Z, hZ, fun w hw => ?_⟩
    rw [← hloc w, ← hvalZ w hw]; ring

  have hb0' : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb0 : (show ↥(Omega.holRing ϖ) from b) ≠ 0 := hb0'
  obtain ⟨gg', hh', hHz, hAH, hGH⟩ := CerednikDrinfeld.Omega.exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc K₀ C hrk ϖ hex hfin
    (show ↥(Omega.holRing ϖ) from a) (show ↥(Omega.holRing ϖ) from b) hb0 z N hD a' b' ha' hb' hbz heq
  let gg : Omega.HolRingOf ϖ ρ := (show Omega.HolRingOf ϖ ρ from gg')
  let hh : Omega.HolRingOf ϖ ρ := (show Omega.HolRingOf ϖ ρ from hh')
  have hHz' : (show ↥(Omega.holRing ϖ) from hh : ↥(Omega.upperHalfPlane K₀ C) → C) z ≠ 0 := hHz
  have hH0 : hh ≠ 0 := by
    intro h0; apply hHz
    have : hh' = 0 := h0
    rw [this]; rfl
  have hHnd : hh ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ) := mem_nonZeroDivisors_of_ne_zero hH0
  have hmk : (Localization.mk a ⟨b, hb⟩ : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk gg ⟨hh, hHnd⟩ := by
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    show hh * a = b * gg
    have : a * hh = b * gg := hAH
    rw [mul_comm hh a]; exact this
  have hxGH : ((eFC x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      Localization.mk gg ⟨hh, hHnd⟩ := hxab.trans hmk
  have hmem : (Localization.mk gg ⟨hh, hHnd⟩ : FractionRing (Omega.HolRingOf ϖ ρ)) ∈ Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ := by
    rw [← hxGH]; exact (eFC x).2
  have hxeq : eFC.symm ⟨Localization.mk gg ⟨hh, hHnd⟩, hmem⟩ = x := by
    apply eFC.injective
    rw [AlgEquiv.apply_symm_apply]
    exact Subtype.ext hxGH.symm

  have hmemx : x ∈ (pt z).toValuationSubring := (hpt1 z x).2 ⟨gg, hh, hHnd, hHz', hxGH⟩

  obtain ⟨hev, hnu⟩ := hpt2 z gg hh hHnd hmem hHz'
  rw [hxeq] at hev hnu
  have hb'z : b' z₀ ≠ 0 := hbz z₀ rfl
  have hFv : Fv z = a' z₀ / b' z₀ := by
    rw [eq_div_iff hb'z, mul_comm, ← hzz]; exact hloc z₀
  have hGz : (show ↥(Omega.holRing ϖ) from gg : ↥(Omega.upperHalfPlane K₀ C) → C) z * b' z₀ = (show ↥(Omega.holRing ϖ) from hh : ↥(Omega.upperHalfPlane K₀ C) → C) z * a' z₀ := hGH z₀ rfl
  refine ⟨hmemx, ?_, ?_⟩
  · rw [hev, hFv, div_eq_div_iff hHz' hb'z]
    calc (show ↥(Omega.holRing ϖ) from gg : ↥(Omega.upperHalfPlane K₀ C) → C) z * b' z₀ = (show ↥(Omega.holRing ϖ) from hh : ↥(Omega.upperHalfPlane K₀ C) → C) z * a' z₀ := hGz
      _ = a' z₀ * (show ↥(Omega.holRing ϖ) from hh : ↥(Omega.upperHalfPlane K₀ C) → C) z := mul_comm _ _
  · rw [hnu, hFv, div_eq_zero_iff, or_iff_left hb'z]
    constructor
    · intro hG0
      have h1 := hGz
      rw [hG0, zero_mul] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left hHz'
    · intro ha0
      have h1 := hGz
      rw [ha0, mul_zero, mul_eq_zero] at h1
      exact h1.resolve_right hb'z

end ESURJ

namespace ESURJ

theorem disc_subset_affinoid (K₀ : Type) [Field K₀] (C : Type) [Field C] [Algebra K₀ C]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ C) (z : C) (n N : ℕ) (hzn : z ∈ Omega.affinoid ϖ n) (hN : n < N) :
    {w : C | Valued.v (w - z) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ⊆ Omega.affinoid ϖ N := by
  intro w hw
  rw [Omega.mem_affinoid_iff'] at hzn ⊢
  have hp1 : Valued.v (algebraMap K₀ C ϖ.ϖ) < 1 := ϖ.lt_one
  have hp0 : 0 < Valued.v (algebraMap K₀ C ϖ.ϖ) := ϖ.pos
  have hinv : 1 ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ := (one_le_inv₀ hp0).2 hp1.le
  have hNn : Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n :=
    pow_lt_pow_right_of_lt_one₀ hp0 hp1 hN
  have hwz : Valued.v (w - z) < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ n := lt_of_le_of_lt hw hNn
  constructor
  ·
    have h1 : Valued.v w ≤ max (Valued.v (w - z)) (Valued.v z) := by
      have := Valuation.map_add Valued.v (w - z) z; rwa [sub_add_cancel] at this
    refine h1.trans (max_le ?_ (hzn.1.trans (pow_le_pow_right₀ hinv hN.le)))
    exact hw.trans ((pow_le_one₀ hp0.le hp1.le).trans (one_le_pow₀ hinv))
  · intro a
    have hza := hzn.2 a

    have hlt : Valued.v (w - z) < Valued.v (z - algebraMap K₀ C a) := lt_of_lt_of_le hwz hza
    have heq : Valued.v (w - algebraMap K₀ C a) = Valued.v (z - algebraMap K₀ C a) := by
      have : w - algebraMap K₀ C a = (z - algebraMap K₀ C a) + (w - z) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ hlt]
    rw [heq]
    exact hNn.le.trans hza

theorem mem_place_and_nonunit_of_germ
    (K₀ : Type) [Field K₀] (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace C] [IsAlgClosed C]
    (ϖ : Omega.PseudoUniformizer K₀ C) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ C a - algebraMap K₀ C t) < (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)] (Γ : Subgroup G)
    (FC : Type) [Field FC] [Algebra C FC]
    (eFC : FC ≃ₐ[C] ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ))
    (pt : ↥(Omega.upperHalfPlane K₀ C) → Place C FC)
    (hpt1 : ∀ (z : ↥(Omega.upperHalfPlane K₀ C)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ C) → C) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩)
    (hpt2 : ∀ (z : ↥(Omega.upperHalfPlane K₀ C)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ C) → C) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ C) → C) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ C) → C) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ C) → C) z = 0))

    {Y : Scheme.{0}} (q : Spec (CommRingCat.of C) ⟶ Y) (U : Y.Opens) (s : Y.presheaf.obj (Opposite.op U))
    (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U) (pt₀ : Spec (CommRingCat.of C))

    (x : FC) (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
    (hxab : ((eFC x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk a ⟨b, hb⟩)

    (z : ↥(Omega.upperHalfPlane K₀ C)) (Over : ↥(Omega.upperHalfPlane K₀ C) → Prop)
    (hOver : ∀ m : ℕ, Set.Finite {w : ↥(Omega.affinoid ϖ m) | ¬ Over ⟨(w : C), Omega.affinoid_subset_upperHalfPlane ϖ m w.2⟩})
    (F : ↥(Omega.upperHalfPlane K₀ C) → C)
    (hEC : ∀ w : ↥(Omega.upperHalfPlane K₀ C), Over w → (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) w * F w = (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) w)
    (hFz : F z = specValue q U s hqU)
    (hloc : ∃ (N : ℕ) (hD : {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ⊆ Omega.upperHalfPlane K₀ C)
        (a' b' : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} → C),
        a' ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ∧ b' ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ∧
        (∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, (w : C) = (z : C) → b' w ≠ 0) ∧
        ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, b' w * F ⟨(w : C), hD w.2⟩ = a' w) :
    x ∈ (pt z).toValuationSubring ∧ (pt z).evalAt x = specValue q U s hqU ∧
      ((Y.presheaf.germ U (q.base pt₀) (hqU (Set.mem_univ pt₀))).hom s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (q.base pt₀)) →
        x ∈ (pt z).toValuationSubring.nonunits) := by
  classical
  obtain ⟨N, hD, a', b', ha', hb', hbz, hlocF⟩ := hloc

  obtain ⟨n, hzn⟩ := hex (z : C) z.2
  set N' : ℕ := max N (n + 1) with hN'
  have hsub : {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} ⊆ {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} := by
    intro w hw
    have hp1 : Valued.v (algebraMap K₀ C ϖ.ϖ) ≤ 1 := ϖ.lt_one.le
    exact le_trans hw (pow_le_pow_right_of_le_one' hp1 (le_max_left N (n + 1)))
  have hD' : {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} ⊆ Omega.upperHalfPlane K₀ C := hsub.trans hD
  have haff : {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} ⊆ Omega.affinoid ϖ N' :=
    disc_subset_affinoid K₀ C ϖ (z : C) n N' hzn (lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right N (n + 1)))

  let ι : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} → ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} := fun w => ⟨(w : C), hsub w.2⟩
  let a'' : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} → C := fun w => a' (ι w)
  let b'' : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} → C := fun w => b' (ι w)
  have ha'' : a'' ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} := Omega.restrict_mem_holOn_of_subset C hsub ha'
  have hb'' : b'' ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} := Omega.restrict_mem_holOn_of_subset C hsub hb'
  have hbz'' : ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'}, (w : C) = (z : C) → b'' w ≠ 0 := fun w hw => hbz (ι w) hw
  have hloc'' : ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'}, b'' w * F ⟨(w : C), hD' w.2⟩ = a'' w := fun w => hlocF (ι w)

  have hZ : ∃ Z : Set ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'}, Z.Finite ∧ ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'}, w ∉ Z →
      (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(w : C), hD' w.2⟩ * F ⟨(w : C), hD' w.2⟩ =
        (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(w : C), hD' w.2⟩ := by
    refine ⟨{w | ¬ Over ⟨(w : C), hD' w.2⟩}, ?_, fun w hw => hEC _ (by rw [Set.mem_setOf_eq, not_not] at hw; exact hw)⟩

    let j : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N'} → ↥(Omega.affinoid ϖ N') := fun w => ⟨(w : C), haff w.2⟩
    have hj : Function.Injective j := fun w w' h => Subtype.ext (by have := congrArg Subtype.val h; exact this)
    refine Set.Finite.of_finite_image (f := j) ?_ (hj.injOn)
    apply (hOver N').subset
    rintro _ ⟨w, hw, rfl⟩
    exact hw

  obtain ⟨hmem, hev, hnu⟩ := mem_place_and_evalAt_eq_of_local_quotient K₀ C hrk ϖ hex hfin G ρ Γ FC eFC pt hpt1 hpt2
    x a b hb hxab z N' hD' a'' b'' ha'' hb'' hbz'' F hloc'' hZ
  refine ⟨hmem, hev.trans hFz, fun hgerm => ?_⟩
  rw [hnu, hFz]
  exact (specValue_eq_zero_iff_germ_mem_maximalIdeal q U s hqU pt₀).2 hgerm

end ESURJ

namespace ESURJ

theorem mem_nonunits_iff_mem_and {K : Type} [Field K] (A : ValuationSubring K) (x : K) :
    x ∈ A.nonunits ↔ x ∈ A ∧ (x = 0 ∨ x⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  · intro h
    refine ⟨(A.valuation_le_one_iff x).1 h.le, ?_⟩
    rcases eq_or_ne x 0 with h0 | h0
    · exact Or.inl h0
    · right
      intro hinv
      have h1 := (A.valuation_le_one_iff x⁻¹).2 hinv
      rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).2 h0)] at h1
      exact absurd h (not_lt.2 h1)
  · rintro ⟨hx, h0 | hinv⟩
    · rw [h0, map_zero]; exact zero_lt_one
    · have hx0 : x ≠ 0 := fun h0 => by apply hinv; rw [h0, inv_zero]; exact A.zero_mem
      by_contra hge
      push_neg at hge
      apply hinv
      rw [← A.valuation_le_one_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hge
end ESURJ

theorem ESURJ.isCurveOver_invariantFieldOf_evenPart

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
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

    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    [CompleteSpace C] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : Omega.IsExhausted ϖ) [IsDomain (Omega.HolRingOf ϖ ρ)]
    (hnc : ∃ x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'),
      x ∉ Set.range (algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))) :
    IsCurveOver C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') ∧
    Algebra.EssFiniteType C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') ∧
    ∃ x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'), Transcendental C x ∧
      FiniteDimensional ↥(IntermediateField.adjoin C ({x} : Set ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))) ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') := by
  classical
  haveI hDVR : IsDiscreteValuationRing 𝒪 := hdvr

  haveI hresfin : Finite (IsLocalRing.ResidueField 𝒪) := by
    have hmax : IsLocalRing.maximalIdeal 𝒪 = Ideal.span {π} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
    have hr0 : Nat.card (𝒪 ⧸ Ideal.span {π}) ≠ 0 := by
      rw [hres]; exact (Fact.out : r.Prime).ne_zero
    haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero hr0
    show Finite (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪)
    exact Finite.of_equiv _ (Ideal.quotEquivOfEq hmax.symm).toEquiv

  have hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap 𝒪 K₀) ↔ Valued.v (algebraMap K₀ C x) ≤ 1 :=
    fun x => (hF.integers x).symm
  have hϖ : algebraMap 𝒪 K₀ π = ϖ.ϖ := by
    apply (algebraMap K₀ C).injective
    rw [← IsScalarTower.algebraMap_apply 𝒪 K₀ C π]
    exact hF.unif

  letI instV : MulAction G (LT.LatticeTree.Vertex 𝒪 K₀) := MulAction.compHom _ ρ
  haveI instGA : Mumford.GraphAction G (BruhatTits.tree 𝒪 K₀) :=
    ⟨fun g _ _ hadj => Mumford.GraphAction.smul_adj (ρ g) hadj⟩
  have hact : Mumford.ActsThrough (LT.LatticeTree.Vertex 𝒪 K₀) ρ := fun g w => rfl

  obtain ⟨-, -, -, -, -, hexch', hiff, hGAΓ, hfinΓ, hQVΓ, hQEΓ, -⟩ :=
    CerednikDrinfeld.map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
      𝒪 hdvr π hπ hcomplete hres hunr K₀ vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt

  have hTP : ∀ g : G, g ∈ Mumford.typePreserving G (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) ↔
      ρ g ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) :=
    fun g => Iff.rfl
  have hΓeq : Γ ⊓ Mumford.typePreserving G (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) = Γ' := by
    ext x
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, hx'⟩
      exact (hiff x hx).2 ((hTP x).1 hx')
    · intro hx
      have hxΓ : x ∈ Γ := ((hΓ' x).1 hx).1
      exact ⟨hxΓ, (hTP x).2 ((hiff x hxΓ).1 hx)⟩
  subst hΓeq

  have hrel : ∀ {α : Type} [MulAction PGL(2, K₀) α] (a b : α),
      (letI : MulAction G α := MulAction.compHom α ρ
       a ∈ MulAction.orbit (↥(Γ.map ρ)) b → a ∈ MulAction.orbit (↥Γ) b) := by
    intro α _ a b hab
    letI : MulAction G α := MulAction.compHom α ρ
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 hab
    obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.1 h.2
    refine MulAction.mem_orbit_iff.2 ⟨⟨γ, hγ⟩, ?_⟩
    show ρ γ • b = (h : PGL(2, K₀)) • b
    rw [hγh]
  haveI : Fintype (Mumford.QuotVert ↥Γ (LT.LatticeTree.Vertex 𝒪 K₀)) := by
    haveI := hQVΓ
    let f : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex 𝒪 K₀) → Mumford.QuotVert ↥Γ (LT.LatticeTree.Vertex 𝒪 K₀) :=
      Quot.lift (fun w : LT.LatticeTree.Vertex 𝒪 K₀ =>
          (Quotient.mk (MulAction.orbitRel (↥Γ) (LT.LatticeTree.Vertex 𝒪 K₀)) w :
            Mumford.QuotVert ↥Γ (LT.LatticeTree.Vertex 𝒪 K₀)))
        (fun a b hab => Quotient.sound (hrel a b hab))
    have hf : Function.Surjective f := by
      intro q
      induction q using Quot.ind with
      | mk w => exact ⟨Quot.mk _ w, rfl⟩
    haveI : Finite (Mumford.QuotVert ↥Γ (LT.LatticeTree.Vertex 𝒪 K₀)) := Finite.of_surjective f hf
    exact Fintype.ofFinite _
  haveI : Fintype (Mumford.QuotEdge ↥Γ (BruhatTits.tree 𝒪 K₀)) := by
    haveI := hQEΓ
    have hrelD : ∀ a b : (BruhatTits.tree 𝒪 K₀).Dart,
        a ∈ MulAction.orbit (↥(Γ.map ρ)) b → a ∈ MulAction.orbit (↥Γ) b := by
      intro a b hab
      obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 hab
      obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.1 h.2
      refine MulAction.mem_orbit_iff.2 ⟨⟨γ, hγ⟩, ?_⟩
      apply SimpleGraph.Dart.ext
      ext
      · show ρ γ • b.fst = (h : PGL(2, K₀)) • b.fst
        rw [hγh]
      · show ρ γ • b.snd = (h : PGL(2, K₀)) • b.snd
        rw [hγh]
    let f : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree 𝒪 K₀) → Mumford.QuotEdge ↥Γ (BruhatTits.tree 𝒪 K₀) :=
      Quot.lift (fun d : (BruhatTits.tree 𝒪 K₀).Dart =>
          (Quotient.mk (MulAction.orbitRel (↥Γ) (BruhatTits.tree 𝒪 K₀).Dart) d :
            Mumford.QuotEdge ↥Γ (BruhatTits.tree 𝒪 K₀)))
        (fun a b hab => Quotient.sound (hrelD a b hab))
    have hf : Function.Surjective f := by
      intro q
      induction q using Quot.ind with
      | mk d => exact ⟨Quot.mk _ d, rfl⟩
    haveI : Finite (Mumford.QuotEdge ↥Γ (BruhatTits.tree 𝒪 K₀)) := Finite.of_surjective f hf
    exact Fintype.ofFinite _

  have hexchG : ∃ γ : G, γ ∈ Γ ∧
      γ ∉ Mumford.typePreserving G (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) := by
    obtain ⟨γ, hγ, hn⟩ := hexch'
    exact ⟨γ, hγ, fun h => hn ((hTP γ).1 h)⟩
  exact CerednikDrinfeld.Omega.isCurveOver_invariantFieldOf_inf_typePreserving_of_exists_relIndex_ne_zero_of_exists_not_mem_range
    K₀ C hrk 𝒪 hR₀ ϖ π hπ hϖ hex G ρ hact Γ hfinΓ hexchG hvtf hnc

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

    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    [CompleteSpace C] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (ψ₀ : Onr →ₐ[𝒪] R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε)

    (htame : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀,
      Valued.v ((Nat.card ↥{g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v} : ℕ) : C) = 1)
    (hex : Omega.IsExhausted ϖ) [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Φ : AdicPoint K₀ π R → {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R})
    (hΦ : (∀ (x : AdicPoint K₀ π R) (n : ℕ),
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ (Φ x).1 =
          (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1) ∧
      Function.Surjective Φ ∧
      (∀ x x' : AdicPoint K₀ π R, Φ x = Φ x' ↔ ∃ γ ∈ Γ', x' = x.act (σ γ)) ∧
      (Function.Injective (fun p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R} =>
          Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1) ∧
        ∀ cpt : Spec (CommRingCat.of C) ⟶ 𝒳, cpt ≫ f = Scheme.specOver C →
          ∃ p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R},
            Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1 = cpt))

    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪))
    (hsC : sC = Spec.map (CommRingCat.ofHom ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀))))
    [IsIntegral (Limits.pullback f sC)]

    (e : ↑(Limits.pullback f sC).functionField →+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))
    (he₀ : (∀ c : C, e (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC) c) =
        algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') c))
    (heval : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
        (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
        ∃ (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
          ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom s) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
              Localization.mk a ⟨b, hb⟩ ∧
          ∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
            ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
              q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
              q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
              ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
                (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) z *
                    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s)) =
                  (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) z)) :
    Function.Surjective e := by
  classical
  haveI := hdvr

  haveI hfinRes : Finite (IsLocalRing.ResidueField 𝒪) := by
    have hmax : IsLocalRing.maximalIdeal 𝒪 = Ideal.span {π} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
    have hfinq : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
    show Finite (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪)
    rw [hmax]; exact hfinq

  have hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap 𝒪 K₀) ↔ Valued.v (algebraMap K₀ C x) ≤ 1 := fun x => (hF.integers x).symm
  have hϖπ : algebraMap 𝒪 K₀ π = ϖ.ϖ := by
    apply (algebraMap K₀ C).injective
    rw [← IsScalarTower.algebraMap_apply, hF.unif]

  have hfin₀ := CerednikDrinfeld.Omega.exists_finset_forall_v_sub_lt_of_finite_residueField K₀ C 𝒪 hR₀ ϖ π hπ hϖπ

  obtain ⟨htp, hGA, hfinD, hQV, hQE, hexch, hiff, hGAΓ, hfinDΓ, hQVΓ, hQEΓ, hidx⟩ :=
    CerednikDrinfeld.map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group 𝒪 hdvr π hπ hcomplete hres hunr K₀
      vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt
  haveI := hGA
  haveI : Fintype (Mumford.QuotVert ↥(Γ'.map ρ) (LT.LatticeTree.Vertex 𝒪 K₀)) := Fintype.ofFinite _
  haveI : Fintype (Mumford.QuotEdge ↥(Γ'.map ρ) (BruhatTits.tree 𝒪 K₀)) := Fintype.ofFinite _

  obtain ⟨s₀, hs₀⟩ := CerednikDrinfeld.exists_functionField_ne_const_of_cerednikDrinfeld_quotient 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr
    hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hvtf hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv
    ϖ hF ψ₀ hrk hval htame hex Φ hΦ sC hsC
  letI algCK : Algebra C ↑(Limits.pullback f sC).functionField := (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC)).toAlgebra
  have halgCK : ∀ c, algebraMap C ↑(Limits.pullback f sC).functionField c = AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC) c :=
    fun c => rfl
  let e' : ↑(Limits.pullback f sC).functionField →ₐ[C] ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') :=
    { toRingHom := e, commutes' := fun c => by rw [halgCK]; exact he₀ c }
  have he' : ∀ y, e' y = e y := fun _ => rfl
  have heinj : Function.Injective e := e.injective
  let E : IntermediateField C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') := e'.fieldRange
  have ht₀E : e s₀ ∈ E := ⟨s₀, rfl⟩
  have hnc : ∃ x : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'), x ∉ Set.range (algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) := by
    refine ⟨e s₀, ?_⟩
    rintro ⟨c, hc⟩
    apply hs₀ c
    apply heinj
    rw [← hc, he₀ c]
  have ht₀ : Transcendental C (e s₀) := by
    intro halg
    haveI : Algebra.IsIntegral C ↥(IntermediateField.adjoin C ({e s₀} : Set ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))) :=
      ⟨fun y => ((IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral).isAlgebraic y).isIntegral⟩
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C)
      (K := ↥(IntermediateField.adjoin C ({e s₀} : Set ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))))).2
      (⟨e s₀, IntermediateField.mem_adjoin_simple_self C (e s₀)⟩ :
        ↥(IntermediateField.adjoin C ({e s₀} : Set ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))))
    have hc' : algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') c = e s₀ := by
      have h2 := congrArg (Subtype.val : ↥(IntermediateField.adjoin C ({e s₀} : Set ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))) → _) hc
      simpa using h2
    apply hs₀ c
    apply heinj
    rw [← hc', he₀ c]

  obtain ⟨hcurveL, hfinTypeL, hfgL⟩ := ESURJ.isCurveOver_invariantFieldOf_evenPart 𝒪 hdvr π hπ hcomplete hres hunr K₀ vdet hvdet G σ Γ hcent hodd
    Γ' hΓ' ρ hρ hvtf hdisc hcocpt ϖ hF hrk hex hnc
  haveI := hcurveL
  haveI := hfinTypeL

  obtain ⟨pt, hpt1, hpt2⟩ := CerednikDrinfeld.Omega.exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving
    K₀ C hrk 𝒪 hR₀ ϖ π hπ hϖπ hex G ρ Γ' htp hfinD ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') (AlgEquiv.refl) hnc

  obtain ⟨hcurveE, hfinTypeE, -⟩ := AlgebraicCurve.isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') E (e s₀) ht₀E ht₀ hfgL
  haveI := hcurveE
  haveI := hfinTypeE
  haveI : Module.Finite ↥E ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') := AlgebraicCurve.finite_intermediateField_of_transcendental_mem C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') E (e s₀) ht₀E ht₀ hfgL
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K₀ C).injective

  have hinj : Function.Injective (fun w : Place C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') => w.restrict ↥E) := by

    have hsurjpt : Function.Surjective pt :=
      CerednikDrinfeld.Omega.surjective_place_invariantFieldOf_of_mem_iff_of_map_le_typePreserving_of_isCurveOver_of_exists_v_le
        K₀ C hrk hval 𝒪 hR₀ ϖ π hπ hϖπ hex G ρ Γ' htp hfinD ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') (AlgEquiv.refl) pt ⟨hpt1, hpt2⟩

    have htame' : ∀ w : LT.LatticeTree.Vertex 𝒪 K₀,
        Valued.v ((Nat.card ↥(MulAction.stabilizer (↥(Γ'.map ρ)) w) : ℕ) : C) = 1 := by
      intro w
      have e1 : Nat.card ↥(MulAction.stabilizer (↥(Γ'.map ρ)) w) = Nat.card ↥{g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • w = w} := by
        apply Nat.card_congr
        exact { toFun := fun g => ⟨(g.1 : PGL(2, K₀)), g.1.2, g.2⟩
                invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
                left_inv := fun g => rfl
                right_inv := fun g => rfl }
      rw [e1]; exact htame w
    have hsep := CerednikDrinfeld.Omega.place_invariantFieldOf_eq_iff_exists_eq_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
        K₀ C hrk hval 𝒪 hR₀ ϖ π hπ hϖπ hex G ρ Γ' htp hfinD htame' ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') (AlgEquiv.refl) pt ⟨hpt1, hpt2⟩

    have hOC : Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ Scheme.specOver (𝒪 := 𝒪) R = sC := by
      rw [hsC, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply 𝒪 R C, ← IsScalarTower.algebraMap_apply 𝒪 K₀ C]
    have cpt : ∀ x : AdicPoint K₀ π R, ∃ q : Spec (CommRingCat.of C) ⟶ (Limits.pullback f sC),
        q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
        q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) := by
      intro x
      refine ⟨Limits.pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1) (𝟙 _) ?_,
        Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
      rw [Category.assoc, (Φ x).2, hOC, Category.id_comp]

    have hOverFin : ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint ((Limits.pullback f sC) : Scheme.{0}) ∈ U) (m : ℕ),
        Set.Finite {w : ↥(Omega.affinoid ϖ m) | ¬ (∃ x : AdicPoint K₀ π R, ((⟨(w : C), Omega.affinoid_subset_upperHalfPlane ϖ m w.2⟩ :
          ↥(Omega.upperHalfPlane K₀ C)) : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ (Limits.pullback f sC), q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧ (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)} := by
      intro U hU m
      have hF' := CerednikDrinfeld.finite_affinoid_toOmega_of_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr
        hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f hsmooth Θ hΘnat hΘinv hΘfib hΘuniv
        ϖ hF ψ₀ hrk hval hex Φ hΦ sC hsC U hU m
      apply hF'.subset
      intro w hw
      simp only [Set.mem_setOf_eq, not_exists, not_and] at hw
      obtain ⟨x, -, hx⟩ := AdicPoint.toOmega_surjOn (C := C) ϖ hF (Omega.affinoid_subset_upperHalfPlane ϖ m w.2)
      obtain ⟨q, hqf, hqs⟩ := cpt x
      refine ⟨x, hx.symm, q, hqf, hqs, ?_⟩
      intro hqU
      exact hw x hx.symm q hqf hqs hqU

    have dom : ∀ (z : ↥(Omega.upperHalfPlane K₀ C)) (x : AdicPoint K₀ π R), (z : C) = x.toOmega C →
        ∀ (q : Spec (CommRingCat.of C) ⟶ (Limits.pullback f sC)),
          q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
          q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
        ∀ g : (Limits.pullback f sC).presheaf.stalk (q.base (IsLocalRing.closedPoint C)),
          e (algebraMap _ ↑(Limits.pullback f sC).functionField g) ∈ (pt z).toValuationSubring ∧
          (g ∈ IsLocalRing.maximalIdeal _ → e (algebraMap _ ↑(Limits.pullback f sC).functionField g) ∈ (pt z).toValuationSubring.nonunits) := by
      intro z x hz q hqf hqs g
      obtain ⟨U, hPU, s, rfl⟩ := TopCat.Presheaf.germ_exist (Limits.pullback f sC).presheaf (x := q.base (IsLocalRing.closedPoint C)) g
      have hU : genericPoint ((Limits.pullback f sC) : Scheme.{0}) ∈ U :=
        ((genericPoint_spec ((Limits.pullback f sC) : Scheme.{0})).mem_open_set_iff U.isOpen).2 ⟨_, Set.mem_univ _, hPU⟩
      have hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U := by
        intro p _
        have hp : p = IsLocalRing.closedPoint C := Subsingleton.elim _ _
        show q.base p ∈ U
        rw [hp]; exact hPU

      obtain ⟨a, b, hb, hab, hECpt⟩ := heval U hU s
      obtain ⟨Fz, hFval, -, -, hFloc⟩ := CerednikDrinfeld.exists_invariant_chartwiseMeromorphic_pullback_of_cerednikDrinfeld_quotient_of_eval_of_smooth 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr
        hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f hsmooth Θ hΘnat hΘinv hΘfib hΘuniv
        ϖ hF ψ₀ hrk hval hex Φ hΦ sC hsC U hU s

      have hgerm : algebraMap _ ↑(Limits.pullback f sC).functionField (((Limits.pullback f sC).presheaf.germ U _ hPU).hom s) =
          ((Limits.pullback f sC).presheaf.germ U (genericPoint ((Limits.pullback f sC) : Scheme.{0})) hU).hom s :=
        TopCat.Presheaf.germ_stalkSpecializes_apply _ hPU (genericPoint_specializes _) s
      rw [hgerm]
      have key := ESURJ.mem_place_and_nonunit_of_germ K₀ C hrk ϖ hex hfin₀ G ρ Γ' ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') (AlgEquiv.refl) pt hpt1 hpt2
        q U s hqU (IsLocalRing.closedPoint C) (e (((Limits.pullback f sC).presheaf.germ U (genericPoint ((Limits.pullback f sC) : Scheme.{0})) hU).hom s)) a b hb
        (by simpa using hab) z
        (fun ζ => ∃ x' : AdicPoint K₀ π R, (ζ : C) = x'.toOmega C ∧
          ∃ q' : Spec (CommRingCat.of C) ⟶ (Limits.pullback f sC), q' ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x').1 ∧
            q' ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧ (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ U)
        (hOverFin U hU) Fz
        (by
          rintro w ⟨x', hw, q', hq'f, hq's, hq'U⟩
          rw [hFval x' w hw q' hq'f hq's hq'U]
          exact hECpt x' w hw q' hq'f hq's hq'U)
        (hFval x z hz q hqf hqs hqU) (hFloc x z hz q hqf hqs hqU)
      exact ⟨key.1, key.2.2⟩

    intro w₁ w₂ hw
    obtain ⟨z₁, rfl⟩ := hsurjpt w₁
    obtain ⟨z₂, rfl⟩ := hsurjpt w₂
    have hwE : ∀ y : ↥E, ((y : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) ∈ (pt z₁).toValuationSubring ↔ (y : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) ∈ (pt z₂).toValuationSubring) := by
      intro y
      have := congrArg Place.toValuationSubring hw
      simp only [Place.restrict_toValuationSubring] at this
      have h1 : y ∈ (pt z₁).toValuationSubring.comap (algebraMap ↥E ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) ↔ y ∈ (pt z₂).toValuationSubring.comap (algebraMap ↥E ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) := by
        rw [this]
      simpa [ValuationSubring.mem_comap] using h1
    have hwEnu : ∀ y : ↥E, ((y : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) ∈ (pt z₁).toValuationSubring.nonunits ↔ (y : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) ∈ (pt z₂).toValuationSubring.nonunits) := by
      intro y
      rw [ESURJ.mem_nonunits_iff_mem_and, ESURJ.mem_nonunits_iff_mem_and, hwE y]
      have hinv : ((y : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'))⁻¹) = ((y⁻¹ : ↥E) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) := by simp
      rw [hinv, hwE (y⁻¹)]

    obtain ⟨x₁, -, hx₁⟩ := AdicPoint.toOmega_surjOn (C := C) ϖ hF z₁.2
    obtain ⟨x₂, -, hx₂⟩ := AdicPoint.toOmega_surjOn (C := C) ϖ hF z₂.2
    beta_reduce at hx₁ hx₂
    obtain ⟨q₁, hq₁f, hq₁s⟩ := cpt x₁
    obtain ⟨q₂, hq₂f, hq₂s⟩ := cpt x₂

    haveI : (Limits.pullback f sC).IsSeparated := by
      have e1 : Limits.terminal.from (Limits.pullback f sC) = Limits.pullback.snd f sC ≫ Limits.terminal.from _ := Limits.terminal.hom_ext _ _
      exact ⟨by rw [e1]; infer_instance⟩
    let Ov : ValuationSubring ↑(Limits.pullback f sC).functionField := ValuationSubring.comap (pt z₁).toValuationSubring e
    have hP : q₁.base (IsLocalRing.closedPoint C) = q₂.base (IsLocalRing.closedPoint C) := by
      apply AlgebraicGeometry.eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated Ov
      · intro g; exact (dom z₁ x₁ hx₁.symm q₁ hq₁f hq₁s g).1
      · intro g hg
        have h1 := (dom z₁ x₁ hx₁.symm q₁ hq₁f hq₁s g).2 hg
        rw [ESURJ.mem_nonunits_iff_mem_and] at h1 ⊢
        refine ⟨h1.1, ?_⟩
        rcases h1.2 with h0 | hni
        · exact Or.inl (e.injective (by rw [h0, map_zero]))
        · right; intro hmem; apply hni
          have : e ((algebraMap _ ↑(Limits.pullback f sC).functionField g)⁻¹) = (e (algebraMap _ ↑(Limits.pullback f sC).functionField g))⁻¹ := map_inv₀ e _
          rw [← this]; exact hmem
      · intro g
        have h1 := (dom z₂ x₂ hx₂.symm q₂ hq₂f hq₂s g).1
        show e (algebraMap _ ↑(Limits.pullback f sC).functionField g) ∈ (pt z₁).toValuationSubring
        exact (hwE ⟨_, ⟨_, rfl⟩⟩).2 h1
      · intro g hg
        have h1 := (dom z₂ x₂ hx₂.symm q₂ hq₂f hq₂s g).2 hg
        have h2 : e (algebraMap _ ↑(Limits.pullback f sC).functionField g) ∈ (pt z₁).toValuationSubring.nonunits := (hwEnu ⟨_, ⟨_, rfl⟩⟩).2 h1
        rw [ESURJ.mem_nonunits_iff_mem_and] at h2 ⊢
        refine ⟨h2.1, ?_⟩
        rcases h2.2 with h0 | hni
        · exact Or.inl (e.injective (by rw [h0, map_zero]))
        · right; intro hmem; apply hni
          have : e ((algebraMap _ ↑(Limits.pullback f sC).functionField g)⁻¹) = (e (algebraMap _ ↑(Limits.pullback f sC).functionField g))⁻¹ := map_inv₀ e _
          rw [← this]; exact hmem

    haveI : LocallyOfFiniteType (Limits.pullback.snd f sC) := by infer_instance
    have hq : q₁ = q₂ :=
      (AlgebraicGeometry.eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed C (Limits.pullback.snd f sC)).1
        q₁ q₂ hq₁s hq₂s hP
    have hΦeq : Φ x₁ = Φ x₂ := by
      apply hΦ.2.2.2.1
      show Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x₁).1 = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x₂).1
      rw [← hq₁f, ← hq₂f, hq]
    obtain ⟨γ, hγ, hx₂eq⟩ := (hΦ.2.2.1 x₁ x₂).1 hΦeq
    apply (hsep z₁ z₂).2
    refine ⟨⟨ρ γ, Subgroup.mem_map_of_mem ρ hγ⟩, Subtype.ext ?_⟩
    rw [Omega.coe_smul_upperHalfPlane]
    show (z₂ : C) = Omega.pmoebius K₀ (ρ γ) (z₁ : C)
    rw [← hx₂, hx₂eq, AdicPoint.toOmega_act ϖ hF, hρ, hx₁]

  have hsurj := AlgebraicCurve.surjective_algebraMap_of_injective_restrict_place_of_isAlgClosed C ↥E ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') hinj
  intro y
  obtain ⟨⟨y', s, hs⟩, hy⟩ := hsurj y
  refine ⟨s, ?_⟩
  rw [← hy]
  show e s = (algebraMap ↥E ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) ⟨y', s, hs⟩
  rw [IntermediateField.algebraMap_apply]
  exact hs

end

end S_CerednikDrinfeld_surjective_ringHom_functionField_invariantFieldOf_of_eval_of_tame_of_cerednikDrinfeld_quotient_of_virtuallyTorsionFree_of_smooth
end P2MW
export P2MW.S_CerednikDrinfeld_surjective_ringHom_functionField_invariantFieldOf_of_eval_of_tame_of_cerednikDrinfeld_quotient_of_virtuallyTorsionFree_of_smooth (solution)
