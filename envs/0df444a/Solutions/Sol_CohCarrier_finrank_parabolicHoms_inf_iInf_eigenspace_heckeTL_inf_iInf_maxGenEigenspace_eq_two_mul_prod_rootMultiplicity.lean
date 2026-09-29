-- Prove2me | solution 1 for CohCarrier.finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d49a3b0f-4d83-53b8-8e59-43c12715b229

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots

import Theorems.Thm_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
import Theorems.Thm_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
import Theorems.Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange
import Theorems.Thm_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp

import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex CuspForm.GammaH_finiteIndex WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one"
p2m_attr_erase "simp" "Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open Polynomial

open scoped TensorProduct

namespace CESCountAux

theorem comap_maxGenEigenspace_eq_of_comm {F : Type} [Field F]
    {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (ι : X →ₗ[F] Y) (hι : Function.Injective ι) (f' : Module.End F X) (f : Module.End F Y)
    (h : ι ∘ₗ f' = f ∘ₗ ι) (μ : F) :
    (f.maxGenEigenspace μ).comap ι = f'.maxGenEigenspace μ := by
  have hc : ∀ y, f (ι y) = ι (f' y) := fun y => (LinearMap.congr_fun h y).symm
  have hk : ∀ (k : ℕ) (x : X), ((f - μ • (1 : Module.End F Y)) ^ k) (ι x) =
      ι (((f' - μ • (1 : Module.End F X)) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [LinearMap.sub_apply, hc]
  ext x
  simp only [Submodule.mem_comap, Module.End.mem_maxGenEigenspace, hk, map_eq_zero_iff ι hι]

theorem comap_eigenspace_eq_of_comm {F : Type} [Field F]
    {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (ι : X →ₗ[F] Y) (hι : Function.Injective ι) (f' : Module.End F X) (f : Module.End F Y)
    (h : ι ∘ₗ f' = f ∘ₗ ι) (μ : F) :
    (f.eigenspace μ).comap ι = f'.eigenspace μ := by
  have hc : ∀ y, f (ι y) = ι (f' y) := fun y => (LinearMap.congr_fun h y).symm
  ext x
  rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, hc, ← map_smul,
    hι.eq_iff]

section basechange

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

noncomputable def coordL (V : Type) [AddCommGroup V] [Module K V] :
    Ω ⊗[K] V ≃ₗ[K] (Module.Basis.ofVectorSpaceIndex K Ω →₀ V) :=
  haveI := Classical.decEq (Module.Basis.ofVectorSpaceIndex K Ω)
  (TensorProduct.congr (Module.Basis.ofVectorSpace K Ω).repr (LinearEquiv.refl K V)).trans
    (TensorProduct.finsuppScalarLeft K V (Module.Basis.ofVectorSpaceIndex K Ω))

theorem coordL_tmul_apply (V : Type) [AddCommGroup V] [Module K V] (c : Ω) (v : V)
    (b : Module.Basis.ofVectorSpaceIndex K Ω) :
    coordL V (c ⊗ₜ[K] v) b = (Module.Basis.ofVectorSpace K Ω).repr c b • v := by
  classical
  simp only [coordL, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.finsuppScalarLeft_apply_tmul]
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single b (fun a _ hab => by simp [hab]) (fun _ => by simp)]
  simp

theorem coordL_baseChange {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (g : V' →ₗ[K] V) (x : Ω ⊗[K] V') (b : Module.Basis.ofVectorSpaceIndex K Ω) :
    coordL V (g.baseChange Ω x) b = g (coordL V' x b) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [coordL_tmul_apply]
  | add x y hx hy => simp [map_add, hx, hy]

theorem coordL_algebraMap_smul (V : Type) [AddCommGroup V] [Module K V] (x : K) (z : Ω ⊗[K] V)
    (b : Module.Basis.ofVectorSpaceIndex K Ω) :
    coordL V (algebraMap K Ω x • z) b = x • coordL V z b := by
  rw [algebraMap_smul, map_smul, Finsupp.smul_apply]

theorem mem_range_baseChange_iff {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (g : V' →ₗ[K] V) (hg : Function.Injective g) (z : Ω ⊗[K] V) :
    z ∈ LinearMap.range (g.baseChange Ω) ↔ ∀ b, coordL V z b ∈ LinearMap.range g := by
  constructor
  · rintro ⟨y, rfl⟩ b
    rw [coordL_baseChange]
    exact LinearMap.mem_range_self g _
  · intro h
    classical
    choose pre hpre using fun b => h b
    let y' : Module.Basis.ofVectorSpaceIndex K Ω →₀ V' :=
      { support := (coordL V z).support
        toFun := fun b => pre b
        mem_support_toFun := fun b => by
          rw [Finsupp.mem_support_iff, ne_eq, ne_eq, ← map_eq_zero_iff g hg, hpre] }
    refine ⟨(coordL V').symm y', ?_⟩
    apply (coordL V).injective
    ext b
    rw [coordL_baseChange, LinearEquiv.apply_symm_apply]
    exact hpre b

theorem mem_range_subtype_baseChange_iff {V : Type} [AddCommGroup V] [Module K V]
    (P : Submodule K V) (z : Ω ⊗[K] V) :
    z ∈ LinearMap.range (P.subtype.baseChange Ω) ↔ ∀ b, coordL V z b ∈ P := by
  rw [mem_range_baseChange_iff P.subtype P.injective_subtype]
  simp only [Submodule.range_subtype]

theorem mem_eigenspace_baseChange_iff {V : Type} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (x : K) (z : Ω ⊗[K] V) :
    z ∈ Module.End.eigenspace (f.baseChange Ω) (algebraMap K Ω x) ↔ ∀ b, coordL V z b ∈ f.eigenspace x := by
  simp only [Module.End.mem_eigenspace_iff]
  constructor
  · intro hz b
    have := congrArg (fun w => coordL V w b) hz
    simp only [coordL_baseChange, coordL_algebraMap_smul] at this
    exact this
  · intro h
    apply (coordL V).injective
    ext b
    rw [coordL_baseChange, coordL_algebraMap_smul]
    exact h b

theorem range_subtype_baseChange_iInf_eigenspace {V : Type} [AddCommGroup V] [Module K V]
    {I : Type} (f : I → Module.End K V) (x : I → K) :
    LinearMap.range ((⨅ i, (f i).eigenspace (x i)).subtype.baseChange Ω) =
      ⨅ i, Module.End.eigenspace ((f i).baseChange Ω) (algebraMap K Ω (x i)) := by
  ext z
  simp only [mem_range_subtype_baseChange_iff, Submodule.mem_iInf, mem_eigenspace_baseChange_iff]
  exact forall_comm

theorem baseChange_injective_of_injective {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (g : V' →ₗ[K] V) (hg : Function.Injective g) :
    Function.Injective (g.baseChange Ω) := by
  intro y y' hyy
  rw [← sub_eq_zero] at hyy ⊢
  rw [← map_sub] at hyy
  generalize y - y' = w at hyy ⊢
  apply (coordL V').injective
  ext b
  have := congrArg (fun u => coordL V u b) hyy
  simp only [coordL_baseChange, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact hg (by rw [this, map_zero])

theorem subtype_baseChange_injective {V : Type} [AddCommGroup V] [Module K V] (P : Submodule K V) :
    Function.Injective (P.subtype.baseChange Ω) :=
  baseChange_injective_of_injective P.subtype P.injective_subtype

end basechange

end CESCountAux

namespace CESCountAux

noncomputable abbrev TL (N : ℕ) (A : Type) [CommRing A] (p : ℕ) (hp : p.Prime) :
    Module.End A (CohCarrier.H1 N ⊤ A) :=
  haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ A p

section jointeig

variable {K : Type} [Field K] {P : Type} [AddCommGroup P] [Module K P] {I : Type}

def JointEig (T' : I → Module.End K P) (x : I → K) : Type :=
  ↥(⨅ i, Module.End.eigenspace (T' i) (x i))

variable (T' : I → Module.End K P) (x : I → K)

scoped instance JointEig.instAddCommGroup : AddCommGroup (JointEig T' x) :=
  inferInstanceAs (AddCommGroup ↥(⨅ i, Module.End.eigenspace (T' i) (x i)))

p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig"
scoped instance JointEig.instModule : Module K (JointEig T' x) :=
  inferInstanceAs (Module K ↥(⨅ i, Module.End.eigenspace (T' i) (x i)))

p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig"
scoped instance JointEig.instFinite [FiniteDimensional K P] : FiniteDimensional K (JointEig T' x) :=
  inferInstanceAs (FiniteDimensional K ↥(⨅ i, Module.End.eigenspace (T' i) (x i)))

p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig"

def JointEig.incl : JointEig T' x →ₗ[K] P := (⨅ i, Module.End.eigenspace (T' i) (x i)).subtype

theorem JointEig.incl_injective : Function.Injective (JointEig.incl T' x) := Subtype.val_injective

theorem JointEig.range_incl : LinearMap.range (JointEig.incl T' x) = ⨅ i, Module.End.eigenspace (T' i) (x i) :=
  Submodule.range_subtype _

def JointEig.op (S : Module.End K P)
    (hW : ∀ w : P, w ∈ (⨅ i, Module.End.eigenspace (T' i) (x i)) → S w ∈ (⨅ i, Module.End.eigenspace (T' i) (x i))) :
    Module.End K (JointEig T' x) := S.restrict hW

theorem JointEig.incl_comp_op (S : Module.End K P)
    (hW : ∀ w : P, w ∈ (⨅ i, Module.End.eigenspace (T' i) (x i)) → S w ∈ (⨅ i, Module.End.eigenspace (T' i) (x i))) :
    JointEig.incl T' x ∘ₗ JointEig.op T' x S hW = S ∘ₗ JointEig.incl T' x := rfl

variable {Ω : Type} [Field Ω] [Algebra K Ω]

theorem JointEig.range_incl_baseChange :
    LinearMap.range ((JointEig.incl T' x).baseChange Ω) =
      ⨅ i, Module.End.eigenspace ((T' i).baseChange Ω) (algebraMap K Ω (x i)) := by
  ext z
  rw [mem_range_baseChange_iff _ (JointEig.incl_injective T' x), JointEig.range_incl]
  simp only [Submodule.mem_iInf, mem_eigenspace_baseChange_iff]
  exact forall_comm

end jointeig
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig"

section transport

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
  {P : Type} [AddCommGroup P] [Module K P] {H : Type} [AddCommGroup H] [Module Ω H]
  (Φ : Ω ⊗[K] P →ₗ[Ω] H) (hΦ : Function.Injective Φ)

include hΦ in

theorem finrank_range_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq
    {I J : Type} (T : I → Module.End Ω H) (T' : I → Module.End K P)
    (hT : ∀ i, T i ∘ₗ Φ = Φ ∘ₗ (T' i).baseChange Ω)
    (S : J → Module.End Ω H) (S' : J → Module.End K P)
    (hS : ∀ j, S j ∘ₗ Φ = Φ ∘ₗ (S' j).baseChange Ω)
    (x : I → K) (lam : J → Ω)
    (hW : ∀ (j : J) (w : P), w ∈ (⨅ i, Module.End.eigenspace (T' i) (x i)) →
      S' j w ∈ (⨅ i, Module.End.eigenspace (T' i) (x i))) :
    Module.finrank Ω ↥(LinearMap.range Φ ⊓ (⨅ i, Module.End.eigenspace (T i) (algebraMap K Ω (x i))) ⊓
        (⨅ j, Module.End.maxGenEigenspace (S j) (lam j))) =
      Module.finrank Ω ↥(⨅ j, Module.End.maxGenEigenspace
        ((JointEig.op T' x (S' j) (hW j)).baseChange Ω) (lam j)) := by
  let Ψ : Ω ⊗[K] JointEig T' x →ₗ[Ω] H := Φ ∘ₗ ((JointEig.incl T' x).baseChange Ω)
  have hΨinj : Function.Injective Ψ :=
    hΦ.comp (baseChange_injective_of_injective _ (JointEig.incl_injective T' x))
  have hcomapT : ∀ i, (Module.End.eigenspace (T i) (algebraMap K Ω (x i))).comap Φ =
      Module.End.eigenspace ((T' i).baseChange Ω) (algebraMap K Ω (x i)) := fun i =>
    comap_eigenspace_eq_of_comm Φ hΦ _ _ (hT i).symm _
  have hrangeΨ : LinearMap.range Ψ =
      LinearMap.range Φ ⊓ ⨅ i, Module.End.eigenspace (T i) (algebraMap K Ω (x i)) := by
    rw [LinearMap.range_comp, JointEig.range_incl_baseChange, ← Submodule.map_comap_eq,
      Submodule.comap_iInf]
    congr 1
    exact (iInf_congr hcomapT).symm
  have hΨS : ∀ j, S j ∘ₗ Ψ = Ψ ∘ₗ ((JointEig.op T' x (S' j) (hW j)).baseChange Ω) := by
    intro j
    calc S j ∘ₗ Ψ = (S j ∘ₗ Φ) ∘ₗ (JointEig.incl T' x).baseChange Ω := by rw [LinearMap.comp_assoc]
      _ = Φ ∘ₗ ((S' j).baseChange Ω ∘ₗ (JointEig.incl T' x).baseChange Ω) := by
          rw [hS j, LinearMap.comp_assoc]
      _ = Φ ∘ₗ ((JointEig.incl T' x).baseChange Ω ∘ₗ (JointEig.op T' x (S' j) (hW j)).baseChange Ω) := by
          rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, JointEig.incl_comp_op]
      _ = Ψ ∘ₗ (JointEig.op T' x (S' j) (hW j)).baseChange Ω := by rw [← LinearMap.comp_assoc]
  have hcomapS : ∀ j, (Module.End.maxGenEigenspace (S j) (lam j)).comap Ψ =
      Module.End.maxGenEigenspace ((JointEig.op T' x (S' j) (hW j)).baseChange Ω) (lam j) := fun j =>
    comap_maxGenEigenspace_eq_of_comm Ψ hΨinj _ _ (hΨS j).symm _
  rw [← hrangeΨ, ← Submodule.map_comap_eq, Submodule.comap_iInf,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Ψ hΨinj _), iInf_congr hcomapS]

end transport
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig"

end CESCountAux
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux"

namespace CESCountAux

section transportA

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
  {P : Type} [AddCommGroup P] [Module K P] {H : Type} [AddCommGroup H] [Module Ω H]
  (Φ : Ω ⊗[K] P →ₗ[Ω] H) (hΦ : Function.Injective Φ)

include hΦ in
theorem inf_maxGenEigenspace_le_eigenspace_of_baseChange
    (p : Submodule Ω H) (hp : LinearMap.range Φ = p)
    (T : Module.End Ω H) (T' : Module.End K P) (hT : T ∘ₗ Φ = Φ ∘ₗ T'.baseChange Ω) (ν : Ω)
    (h : Module.End.maxGenEigenspace (T'.baseChange Ω) ν ≤ Module.End.eigenspace (T'.baseChange Ω) ν) :
    p ⊓ Module.End.maxGenEigenspace T ν ≤ Module.End.eigenspace T ν := by
  rw [← hp, ← Submodule.map_comap_eq, comap_maxGenEigenspace_eq_of_comm Φ hΦ _ _ hT.symm]
  calc Submodule.map Φ (Module.End.maxGenEigenspace (T'.baseChange Ω) ν)
      ≤ Submodule.map Φ (Module.End.eigenspace (T'.baseChange Ω) ν) := Submodule.map_mono h
    _ = Submodule.map Φ ((Module.End.eigenspace T ν).comap Φ) := by
        rw [comap_eigenspace_eq_of_comm Φ hΦ _ _ hT.symm]
    _ ≤ Module.End.eigenspace T ν := Submodule.map_comap_le _ _

include hΦ in
theorem maxGenEigenspace_baseChange_le_eigenspace_of_inf_le
    (p : Submodule Ω H) (hp : LinearMap.range Φ = p)
    (T : Module.End Ω H) (T' : Module.End K P) (hT : T ∘ₗ Φ = Φ ∘ₗ T'.baseChange Ω) (ν : Ω)
    (h : p ⊓ Module.End.maxGenEigenspace T ν ≤ Module.End.eigenspace T ν) :
    Module.End.maxGenEigenspace (T'.baseChange Ω) ν ≤ Module.End.eigenspace (T'.baseChange Ω) ν := by
  rw [← comap_maxGenEigenspace_eq_of_comm Φ hΦ _ _ hT.symm, ← comap_eigenspace_eq_of_comm Φ hΦ _ _ hT.symm]
  intro z hz
  exact h ⟨hp ▸ LinearMap.mem_range_self Φ z, hz⟩

end transportA
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux"

theorem iInf_prop_prop_eq_iInf_subtype {α : Type} [CompleteLattice α] {p s : ℕ → Prop}
    (f : (n : ℕ) → p n → α) :
    (⨅ (n : ℕ) (hn : p n) (_ : s n), f n hn) = ⨅ i : {n : ℕ // p n ∧ s n}, f i.1 i.2.1 := by
  apply le_antisymm
  · exact le_iInf fun i => (iInf_le _ i.1).trans ((iInf_le _ i.2.1).trans (iInf_le _ i.2.2))
  · refine le_iInf fun n => le_iInf fun hn => le_iInf fun hs => ?_
    exact iInf_le (fun i : {n : ℕ // p n ∧ s n} => f i.1 i.2.1) ⟨n, hn, hs⟩

theorem iInf_prop_prop_dep_eq_iInf_subtype {α : Type} [CompleteLattice α] {p s : ℕ → Prop}
    (f : (n : ℕ) → p n → s n → α) :
    (⨅ (n : ℕ) (hn : p n) (hs : s n), f n hn hs) = ⨅ i : {n : ℕ // p n ∧ s n}, f i.1 i.2.1 i.2.2 := by
  apply le_antisymm
  · exact le_iInf fun i => (iInf_le _ i.1).trans ((iInf_le _ i.2.1).trans (iInf_le _ i.2.2))
  · refine le_iInf fun n => le_iInf fun hn => le_iInf fun hs => ?_
    exact iInf_le (fun i : {n : ℕ // p n ∧ s n} => f i.1 i.2.1 i.2.2) ⟨n, hn, hs⟩

end CESCountAux
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux"

namespace CESCountAux

theorem count_transport (N : ℕ) [NeZero N] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (hpar : ∀ (p : ℕ) (hp : p.Prime) (w : CohCarrier.H1 N ⊤ K),
        w ∈ ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K →
          (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p) w ∈
            ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K)
    (Φ : Ω ⊗[K] ↥(ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K) →ₗ[Ω] CohCarrier.H1 N ⊤ Ω)
    (hinj : Function.Injective Φ)
    (hrange : LinearMap.range Φ = ModularCurve.Period.parabolicHoms Ω (CohCarrier.GammaH N ⊤) Ω)
    (hT : ∀ (p : ℕ) (hp : p.Prime),
        (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ Ω p) ∘ₗ Φ =
          Φ ∘ₗ ((haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeTL N ⊤ K p).restrict (hpar p hp)).baseChange Ω)
    {I J : Type} (ℓ : I → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (q : J → ℕ) (hq : ∀ j, (q j).Prime)
    (x : I → K) (lam : J → Ω)
    (hW : ∀ (j : J) (w : ↥(ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K)),
      w ∈ (⨅ i, Module.End.eigenspace ((TL N K (ℓ i) (hℓ i)).restrict (hpar (ℓ i) (hℓ i))) (x i)) →
        (TL N K (q j) (hq j)).restrict (hpar (q j) (hq j)) w ∈
          (⨅ i, Module.End.eigenspace ((TL N K (ℓ i) (hℓ i)).restrict (hpar (ℓ i) (hℓ i))) (x i))) :
    Module.finrank Ω
      ↥(ModularCurve.Period.parabolicHoms Ω (CohCarrier.GammaH N ⊤) Ω ⊓
        (⨅ i, Module.End.eigenspace (TL N Ω (ℓ i) (hℓ i)) (algebraMap K Ω (x i))) ⊓
        (⨅ j, Module.End.maxGenEigenspace (TL N Ω (q j) (hq j)) (lam j))) =
      Module.finrank Ω ↥(⨅ j, Module.End.maxGenEigenspace
        ((JointEig.op (fun i => (TL N K (ℓ i) (hℓ i)).restrict (hpar (ℓ i) (hℓ i))) x
          ((TL N K (q j) (hq j)).restrict (hpar (q j) (hq j))) (hW j)).baseChange Ω) (lam j)) := by
  rw [← hrange]
  exact finrank_range_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq Φ hinj
    (fun i => TL N Ω (ℓ i) (hℓ i)) (fun i => (TL N K (ℓ i) (hℓ i)).restrict (hpar (ℓ i) (hℓ i)))
    (fun i => hT (ℓ i) (hℓ i))
    (fun j => TL N Ω (q j) (hq j)) (fun j => (TL N K (q j) (hq j)).restrict (hpar (q j) (hq j)))
    (fun j => hT (q j) (hq j)) x lam hW

end CESCountAux
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux"

namespace CESCountAux

open Polynomial in

theorem map_localPoly {K L : Type} [Field K] [Field L] (φ : K →+* L) (e : ℕ) (a c : K) :
    (if e = 0 then X - C a else X ^ (e - 1) * (X ^ 2 - C a * X + C c)).map φ =
      if e = 0 then X - C (φ a) else X ^ (e - 1) * (X ^ 2 - C (φ a) * X + C (φ c)) := by
  split_ifs with h
  · rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_C]

end CESCountAux
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux"

namespace CESCountAux

theorem h1_of_countC (N : ℕ) [NeZero N] (S : Finset ℕ) (Mg : ℕ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2)
    {K : Type} [Field K] [Algebra K ℂ]
    (xK : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S} → K)
    (hxC : ∀ i, algebraMap K ℂ (xK i) = ModularFormClass.qCoeff g i)
    [Fintype {q : ℕ // q.Prime ∧ q ∣ N}]
    (aK : {q : ℕ // q.Prime ∧ q ∣ N} → K)
    (haC : ∀ j, algebraMap K ℂ (aK j) = ModularFormClass.qCoeff g j)
    (Dc : ({q : ℕ // q.Prime ∧ q ∣ N} → ℂ) → ℕ)
    (countC : ∀ mu' : {q : ℕ // q.Prime ∧ q ∣ N} → ℂ, Module.finrank ℂ
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ ⊓
        (⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, Module.End.eigenspace (TL N ℂ i i.2.1) (algebraMap K ℂ (xK i))) ⊓
        (⨅ j : {q : ℕ // q.Prime ∧ q ∣ N}, Module.End.maxGenEigenspace (TL N ℂ j j.2.1) (mu' j))) =
      Dc mu')
    (hCC : ∀ mu : ℕ → ℂ, Module.finrank ℂ
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ ⊓
        (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ∉ S), Module.End.eigenspace
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) (ModularFormClass.qCoeff g ℓ)) ⊓
        (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), Module.End.maxGenEigenspace
          (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ q) (mu q))) =
      2 * ∏ q ∈ N.primeFactors, Polynomial.rootMultiplicity (mu q)
        (let e : ℕ := N.factorization q - Mg.factorization q
         if e = 0 then X - C (ModularFormClass.qCoeff g q)
         else X ^ (e - 1) * (X ^ 2 - C (ModularFormClass.qCoeff g q) * X +
           C (if q ∣ Mg then (0 : ℂ) else (q : ℂ)))))
    (μ : {q : ℕ // q.Prime ∧ q ∣ N} → ℂ) :
    Dc μ =
      2 * ∏ j : {q : ℕ // q.Prime ∧ q ∣ N}, Polynomial.rootMultiplicity (μ j)
        ((if N.factorization j - Mg.factorization j = 0 then X - C (aK j)
          else X ^ (N.factorization j - Mg.factorization j - 1) *
            (X ^ 2 - C (aK j) * X + C (if (j : ℕ) ∣ Mg then (0 : K) else ((j : ℕ) : K)))).map
          (algebraMap K ℂ)) := by
  let mu : ℕ → ℂ := fun q => if h : q.Prime ∧ q ∣ N then μ ⟨q, h⟩ else 0
  have hmu : ∀ j : {q : ℕ // q.Prime ∧ q ∣ N}, mu j = μ j := fun j => by
    show dite _ _ _ = _
    rw [dif_pos j.2]
  have hB := hCC mu
  rw [← countC μ]
  have e1 := iInf_prop_prop_eq_iInf_subtype (p := Nat.Prime) (s := fun ℓ => ℓ ∉ S)
    (fun (ℓ : ℕ) (hℓ : ℓ.Prime) => Module.End.eigenspace
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) (ModularFormClass.qCoeff g ℓ))
  have e2 := iInf_prop_prop_eq_iInf_subtype (p := Nat.Prime) (s := fun q => q ∣ N)
    (fun (q : ℕ) (hq : q.Prime) => Module.End.maxGenEigenspace
      (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ q) (mu q))
  rw [e1, e2] at hB
  have hL : (⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S},
      Module.End.eigenspace (TL N ℂ i i.2.1) (algebraMap K ℂ (xK i))) =
      ⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, Module.End.eigenspace
        (haveI : NeZero (i : ℕ) := ⟨i.2.1.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ i) (ModularFormClass.qCoeff g i) :=
    iInf_congr fun i => by rw [hxC i]
  have hM : (⨅ j : {q : ℕ // q.Prime ∧ q ∣ N}, Module.End.maxGenEigenspace (TL N ℂ j j.2.1) (μ j)) =
      ⨅ j : {q : ℕ // q.Prime ∧ q ∣ N}, Module.End.maxGenEigenspace
        (haveI : NeZero (j : ℕ) := ⟨j.2.1.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ j) (mu j) :=
    iInf_congr fun j => by rw [hmu j]
  rw [hL, hM, hB]
  congr 1
  have hNz : N ≠ 0 := NeZero.ne N
  rw [Finset.prod_subtype (p := fun q => q.Prime ∧ q ∣ N) N.primeFactors (fun q => by
    rw [Nat.mem_primeFactors]; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hNz⟩⟩)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hc : algebraMap K ℂ (if (j : ℕ) ∣ Mg then (0 : K) else ((j : ℕ) : K)) =
      if (j : ℕ) ∣ Mg then (0 : ℂ) else ((j : ℕ) : ℂ) := by
    split_ifs <;> simp
  rw [hmu j, map_localPoly, haC j, hc]

theorem faceB_of_countF (N : ℕ) [NeZero N] (S : Finset ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (F : Type) [Field F] (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ) (ι : chig.range →+* F) (lam : ℕ → F)
    {K : Type} [Field K] [Algebra K F]
    (xK : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S} → K)
    (hxF : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, algebraMap K F (xK i) =
      ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T i.2.1
        (fun h => i.2.2 (hNS i i.2.1 (h.trans hMgN))) (Set.notMem_empty (i : ℕ)))))
    [Fintype {q : ℕ // q.Prime ∧ q ∣ N}]
    (aK : {q : ℕ // q.Prime ∧ q ∣ N} → K)
    (haF : ∀ j : {q : ℕ // q.Prime ∧ q ∣ N}, algebraMap K F (aK j) = (if hqMg : (j : ℕ) ∣ Mg
      then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U j.2.1 hqMg (Set.notMem_empty (j : ℕ))))
      else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T j.2.1 hqMg (Set.notMem_empty (j : ℕ))))))
    (d : ℕ)
    (countF : Module.finrank F
      ↥(ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F ⊓
        (⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, Module.End.eigenspace (TL N F i i.2.1) (algebraMap K F (xK i))) ⊓
        (⨅ j : {q : ℕ // q.Prime ∧ q ∣ N}, Module.End.maxGenEigenspace (TL N F j j.2.1) (lam j))) = d)
    (hT1 : d =
      2 * ∏ j : {q : ℕ // q.Prime ∧ q ∣ N}, Polynomial.rootMultiplicity (lam j)
        ((if N.factorization j - Mg.factorization j = 0 then X - C (aK j)
          else X ^ (N.factorization j - Mg.factorization j - 1) *
            (X ^ 2 - C (aK j) * X + C (if (j : ℕ) ∣ Mg then (0 : K) else ((j : ℕ) : K)))).map
          (algebraMap K F))) :
    Module.finrank F
      ↥(ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F ⊓
        (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S), Module.End.eigenspace
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ)
          (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
            (fun h => hℓS (hNS ℓ hℓ (h.trans hMgN))) (Set.notMem_empty ℓ))))) ⊓
        (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), Module.End.maxGenEigenspace
          (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ F q) (lam q))) =
    2 * ∏ q ∈ N.primeFactors, Polynomial.rootMultiplicity (lam q)
      (if hq : q.Prime then
        (let aq : F := if hqMg : q ∣ Mg
            then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)))
            else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hq hqMg (Set.notMem_empty q)))
         let e : ℕ := N.factorization q - Mg.factorization q
         if e = 0 then X - C aq
         else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : F) else (q : F))))
       else 1) := by
  have e1 := iInf_prop_prop_dep_eq_iInf_subtype (p := Nat.Prime) (s := fun ℓ => ℓ ∉ S)
    (fun (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) => Module.End.eigenspace
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ)
      (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
        (fun h => hℓS (hNS ℓ hℓ (h.trans hMgN))) (Set.notMem_empty ℓ)))))
  have e2 := iInf_prop_prop_eq_iInf_subtype (p := Nat.Prime) (s := fun q => q ∣ N)
    (fun (q : ℕ) (hq : q.Prime) => Module.End.maxGenEigenspace
      (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ F q) (lam q))
  rw [e1, e2]
  have hL : (⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, Module.End.eigenspace
        (haveI : NeZero (i : ℕ) := ⟨i.2.1.ne_zero⟩; CohCarrier.heckeTL N ⊤ F i)
        (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T i.2.1
          (fun h => i.2.2 (hNS i i.2.1 (h.trans hMgN))) (Set.notMem_empty (i : ℕ)))))) =
      ⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, Module.End.eigenspace (TL N F i i.2.1) (algebraMap K F (xK i)) :=
    iInf_congr fun i => by rw [hxF i]
  rw [hL, countF, hT1]
  congr 1
  have hNz : N ≠ 0 := NeZero.ne N
  rw [Finset.prod_subtype (p := fun q => q.Prime ∧ q ∣ N) N.primeFactors (fun q => by
    rw [Nat.mem_primeFactors]; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hNz⟩⟩)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hc : algebraMap K F (if (j : ℕ) ∣ Mg then (0 : K) else ((j : ℕ) : K)) =
      if (j : ℕ) ∣ Mg then (0 : F) else ((j : ℕ) : F) := by
    split_ifs <;> simp
  rw [dif_pos j.2.1, map_localPoly, haF j, hc]

end CESCountAux
p2m_reactivate "P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux.JointEig P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.CESCountAux"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
    (hchigT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
    (hchigU : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg),
      chig (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = ModularFormClass.qCoeff g q)
    (ι : chig.range →+* F) (lam : ℕ → F) :

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ μ : F,
      ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F ⊓
          Module.End.maxGenEigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ) μ ≤
        Module.End.eigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ) μ) ∧

    Module.finrank F
      ↥(ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH N ⊤) F ⊓
        (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S), Module.End.eigenspace
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ F ℓ)
          (ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
            (fun h => hℓS (hNS ℓ hℓ (h.trans hMgN))) (Set.notMem_empty ℓ))))) ⊓
        (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), Module.End.maxGenEigenspace
          (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ F q) (lam q))) =
    2 * ∏ q ∈ N.primeFactors, Polynomial.rootMultiplicity (lam q)
      (if hq : q.Prime then
        (let aq : F := if hqMg : q ∣ Mg
            then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)))
            else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hq hqMg (Set.notMem_empty q)))
         let e : ℕ := N.factorization q - Mg.factorization q
         if e = 0 then X - C aq
         else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : F) else (q : F))))
       else 1) := by
  classical

  haveI hfin : Module.Finite ℤ ↥(CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two Mg ∅
  let R : Subring ℂ := chig.range
  haveI : Algebra.IsIntegral ℤ ↥R := by
    haveI : Algebra.IsIntegral ℤ ↥(CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ)) := Algebra.IsIntegral.of_finite ℤ _
    refine ⟨fun r => ?_⟩
    obtain ⟨t, ht⟩ := chig.mem_range.mp r.2
    have hint : IsIntegral ℤ t := Algebra.IsIntegral.isIntegral t
    have := hint.map chig.rangeRestrict.toIntAlgHom
    convert this using 1
    exact Subtype.ext ht.symm
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hne
    have hker : RingHom.ker ι ≠ ⊥ := fun h => hne (by simpa [h] using (RingHom.mem_ker).mpr hr)
    haveI : (RingHom.ker ι).IsPrime := RingHom.ker_isPrime ι
    have hbot : (RingHom.ker ι).comap (algebraMap ℤ ↥R) = ⊥ := by
      rw [eq_bot_iff]
      intro n hn
      rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
      rw [hn]
      exact Ideal.zero_mem _
    exact hker (Ideal.eq_bot_of_comap_eq_bot hbot)
  let K : Type := FractionRing ↥R
  letI algKC : Algebra K ℂ := (IsFractionRing.lift (K := K) (g := R.subtype) Subtype.val_injective).toAlgebra
  letI algKF : Algebra K F := (IsFractionRing.lift (K := K) (g := ι) hιinj).toAlgebra
  have hKC : ∀ r : ↥R, algebraMap K ℂ (algebraMap (↥R) K r) = (r : ℂ) := fun r =>
    IsFractionRing.lift_algebraMap (K := K) Subtype.val_injective r
  have hKF : ∀ r : ↥R, algebraMap K F (algebraMap (↥R) K r) = ι r := fun r =>
    IsFractionRing.lift_algebraMap (K := K) hιinj r

  obtain ⟨hpar, ΦF, hcomm, hinjF, hrangeF, hTF⟩ :=
    CohCarrier.exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange N K F
  obtain ⟨hpar', ΦC, -, hinjC, hrangeC, hTC⟩ :=
    CohCarrier.exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange N K ℂ
  haveI : (CohCarrier.GammaH N ⊤).FiniteIndex := by
    rw [CohCarrier.GammaH_top]; infer_instance
  haveI hfdpar : FiniteDimensional K ↥(ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K) := by
    obtain ⟨n, b, hb⟩ :=
      ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (CohCarrier.GammaH N ⊤)
    obtain ⟨bK, -⟩ := hb K
    exact Module.Finite.of_basis bK

  haveI fJ : Fintype {q : ℕ // q.Prime ∧ q ∣ N} := Fintype.ofFinset N.primeFactors (fun q => by
    rw [Nat.mem_primeFactors]; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, NeZero.ne N⟩⟩)
  have hIMg : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, ¬ (i : ℕ) ∣ Mg := fun i h => i.2.2 (hNS i i.2.1 (h.trans hMgN))
  let xK : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S} → K := fun i => algebraMap (↥R) K (chig.rangeRestrict
    (CuspForm.heckeAlgebra.T i.2.1 (hIMg i) (Set.notMem_empty (i : ℕ))))
  let aK : {q : ℕ // q.Prime ∧ q ∣ N} → K := fun j => if hqMg : (j : ℕ) ∣ Mg
      then algebraMap (↥R) K (chig.rangeRestrict
        (CuspForm.heckeAlgebra.U j.2.1 hqMg (Set.notMem_empty (j : ℕ))))
      else algebraMap (↥R) K (chig.rangeRestrict
        (CuspForm.heckeAlgebra.T j.2.1 hqMg (Set.notMem_empty (j : ℕ))))

  have hxC : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, algebraMap K ℂ (xK i) = ModularFormClass.qCoeff g i := fun i => by
    show algebraMap K ℂ (algebraMap (↥R) K _) = _
    rw [hKC, RingHom.coe_rangeRestrict, hchigT]
  have haC : ∀ j : {q : ℕ // q.Prime ∧ q ∣ N}, algebraMap K ℂ (aK j) = ModularFormClass.qCoeff g j := fun j => by
    show algebraMap K ℂ (dite _ _ _) = _
    split_ifs with hqMg
    · rw [hKC, RingHom.coe_rangeRestrict, hchigU]
    · rw [hKC, RingHom.coe_rangeRestrict, hchigT]
  have haF : ∀ j : {q : ℕ // q.Prime ∧ q ∣ N}, algebraMap K F (aK j) = (if hqMg : (j : ℕ) ∣ Mg
      then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U j.2.1 hqMg (Set.notMem_empty (j : ℕ))))
      else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T j.2.1 hqMg (Set.notMem_empty (j : ℕ))))) := fun j => by
    show algebraMap K F (dite _ _ _) = _
    split_ifs with hqMg
    · rw [hKF]
    · rw [hKF]

  have hWK : ∀ (j : {q : ℕ // q.Prime ∧ q ∣ N}) (w : ↥(ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH N ⊤) K)),
      w ∈ (⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, Module.End.eigenspace
        ((CESCountAux.TL N K i i.2.1).restrict (hpar i i.2.1)) (xK i)) →
      (CESCountAux.TL N K j j.2.1).restrict (hpar j j.2.1) w ∈
        (⨅ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, Module.End.eigenspace
          ((CESCountAux.TL N K i i.2.1).restrict (hpar i i.2.1)) (xK i)) := by
    intro j w hw
    rw [Submodule.mem_iInf] at hw ⊢
    intro i
    have hc := hcomm i j i.2.1 j.2.1
    have hwi := hw i
    rw [Module.End.mem_eigenspace_iff] at hwi ⊢
    show ((CESCountAux.TL N K i i.2.1).restrict (hpar i i.2.1) *
      (CESCountAux.TL N K j j.2.1).restrict (hpar j j.2.1)) w = _
    rw [hc.eq, Module.End.mul_apply, hwi, map_smul]

  have countF := fun lam' : {q : ℕ // q.Prime ∧ q ∣ N} → F => CESCountAux.count_transport N K F hpar ΦF hinjF hrangeF hTF
    (fun i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S} => (i : ℕ)) (fun i => i.2.1) (fun j : {q : ℕ // q.Prime ∧ q ∣ N} => (j : ℕ)) (fun j => j.2.1) xK lam' hWK
  have countC := fun mu' : {q : ℕ // q.Prime ∧ q ∣ N} → ℂ => CESCountAux.count_transport N K ℂ hpar ΦC hinjC hrangeC
    (fun p hp => hTC p hp) (fun i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S} => (i : ℕ)) (fun i => i.2.1) (fun j : {q : ℕ // q.Prime ∧ q ∣ N} => (j : ℕ)) (fun j => j.2.1)
    xK mu' hWK

  have hxF : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}, algebraMap K F (xK i) = ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T i.2.1
      (fun h => i.2.2 (hNS i i.2.1 (h.trans hMgN))) (Set.notMem_empty (i : ℕ)))) := fun i => hKF _
  have h₁ := CESCountAux.h1_of_countC N S Mg g xK hxC aK haC
    (fun mu' => Module.finrank ℂ ↥(⨅ j : {q : ℕ // q.Prime ∧ q ∣ N}, Module.End.maxGenEigenspace
      ((CESCountAux.JointEig.op (fun i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S} => (CESCountAux.TL N K i i.2.1).restrict (hpar i i.2.1)) xK
      ((CESCountAux.TL N K j j.2.1).restrict (hpar j j.2.1)) (hWK j)).baseChange ℂ) (mu' j)))
    countC
    (fun mu => (CohCarrier.finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
      N S hS hNS Mg hMgN g hg mu).2)
  have hT1 := Module.End.finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
    (fun j : {q : ℕ // q.Prime ∧ q ∣ N} => CESCountAux.JointEig.op (fun i : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S} => (CESCountAux.TL N K i i.2.1).restrict (hpar i i.2.1)) xK
      ((CESCountAux.TL N K j j.2.1).restrict (hpar j j.2.1)) (hWK j))
    (fun j : {q : ℕ // q.Prime ∧ q ∣ N} => if N.factorization j - Mg.factorization j = 0 then X - C (aK j)
      else X ^ (N.factorization j - Mg.factorization j - 1) *
        (X ^ 2 - C (aK j) * X + C (if (j : ℕ) ∣ Mg then (0 : K) else ((j : ℕ) : K))))
    2 ℂ h₁ F (fun j : {q : ℕ // q.Prime ∧ q ∣ N} => lam j)
  refine ⟨?_, CESCountAux.faceB_of_countF N S hNS F Mg hMgN chig ι lam xK hxF aK haF _
    (countF (fun j : {q : ℕ // q.Prime ∧ q ∣ N} => lam j)) hT1⟩

  intro ℓ hℓ hℓS ν
  have hAC := (CohCarrier.finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
    N S hS hNS Mg hMgN g hg (fun _ => 0)).1
  have hℓN : ¬ ℓ ∣ N := fun h => hℓS (hNS ℓ hℓ h)
  have hC : ∀ ν' : ℂ, Module.End.maxGenEigenspace
      (((CESCountAux.TL N K ℓ hℓ).restrict (hpar ℓ hℓ)).baseChange ℂ) ν' ≤
      Module.End.eigenspace (((CESCountAux.TL N K ℓ hℓ).restrict (hpar ℓ hℓ)).baseChange ℂ) ν' := fun ν' =>
    CESCountAux.maxGenEigenspace_baseChange_le_eigenspace_of_inf_le ΦC hinjC _ hrangeC
      (CESCountAux.TL N ℂ ℓ hℓ) _ (hTC ℓ hℓ) ν' (hAC ℓ hℓ hℓN ν')
  have hF := Module.End.maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
    ((CESCountAux.TL N K ℓ hℓ).restrict (hpar ℓ hℓ)) ℂ hC F ν
  exact CESCountAux.inf_maxGenEigenspace_le_eigenspace_of_baseChange ΦF hinjF _ hrangeF
    (CESCountAux.TL N F ℓ hℓ) _ (hTF ℓ hℓ) ν hF

end S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
end P2MW
export P2MW.S_CohCarrier_finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity (solution)
