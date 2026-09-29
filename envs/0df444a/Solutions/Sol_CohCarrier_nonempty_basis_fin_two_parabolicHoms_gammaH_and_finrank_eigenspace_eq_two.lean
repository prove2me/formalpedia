-- Prove2me | solution 1 for CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9161ed73-329f-5e35-bd24-7329ae6280bf

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_PeriodHomPair
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_gammaH
import Theorems.Thm_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero"
p2m_attr_erase "simp" "CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

noncomputable section

open ModularCurve.Period

namespace ESGH

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

private abbrev S2 : Type := CuspForm (CohCarrier.GammaH M H) 2

private abbrev V : Type := ↥(parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)

scoped instance instAddCommGroupV : AddCommGroup (V M H) := Submodule.addCommGroup _

scoped instance (priority := 10000) instAddCommMonoidV : AddCommMonoid (V M H) :=
  (instAddCommGroupV M H).toAddCommMonoid

variable (S : Set ℕ)

private def Gf : Set (Module.End ℂ (S2 M H)) :=
  {T | (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
       (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
       (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}

private abbrev 𝔸 : Subalgebra ℂ (Module.End ℂ (S2 M H)) := Algebra.adjoin ℂ (Gf M H S)

private def Gc : Set (Module.End ℂ (V M H)) :=
  {T : Module.End ℂ (V M H) |
    (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      ((T v : V M H) : CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
    (∃ d : (ZMod M)ˣ, ∀ v,
      ((T v : V M H) : CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}

private def A : Subalgebra ℂ (Module.End ℂ (V M H)) := Algebra.adjoin ℂ (Gc M H S)

private theorem A_def : A M H S = Algebra.adjoin ℂ (Gc M H S) := rfl

section Psi

variable {M H}
variable (E : (S2 M H × S2 M H) ≃ₗ[ℂ] V M H)

private def Ψ : Module.End ℂ (S2 M H) →ₐ[ℂ] Module.End ℂ (V M H) where
  toFun t := E.toLinearMap ∘ₗ (t.prodMap t) ∘ₗ E.symm.toLinearMap
  map_one' := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap 1 1 (E.symm v)) = v
    rw [LinearMap.prodMap_one]
    exact E.apply_symm_apply v
  map_mul' s t := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (s * t) (s * t) (E.symm v)) =
      E (LinearMap.prodMap s s (E.symm (E (LinearMap.prodMap t t (E.symm v)))))
    rw [E.symm_apply_apply]
    rfl
  map_zero' := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap 0 0 (E.symm v)) = 0
    rw [LinearMap.prodMap_zero, LinearMap.zero_apply, map_zero]
  map_add' s t := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (s + t) (s + t) (E.symm v)) =
      E (LinearMap.prodMap s s (E.symm v)) + E (LinearMap.prodMap t t (E.symm v))
    rw [← map_add]
    rfl
  commutes' c := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (algebraMap ℂ (Module.End ℂ (S2 M H)) c)
      (algebraMap ℂ (Module.End ℂ (S2 M H)) c) (E.symm v)) = (algebraMap ℂ (Module.End ℂ (V M H)) c) v
    rw [Module.algebraMap_end_eq_smul_id, Module.algebraMap_end_eq_smul_id]
    change E (c • (E.symm v).1, c • (E.symm v).2) = c • v
    rw [← Prod.smul_mk, map_smul]
    exact congrArg (c • ·) (E.apply_symm_apply v)

private theorem Ψ_apply_E (t : Module.End ℂ (S2 M H)) (f g : S2 M H) : Ψ E t (E (f, g)) = E (t f, t g) := by
  change E (LinearMap.prodMap t t (E.symm (E (f, g)))) = _
  rw [E.symm_apply_apply]
  rfl

private theorem Ψ_injective : Function.Injective (Ψ E) := by
  intro s t h
  apply LinearMap.ext
  intro f
  have := congrArg (fun x : Module.End ℂ (V M H) => (E.symm (x (E (f, 0)))).1) h
  simp only [Ψ_apply_E, LinearEquiv.symm_apply_apply] at this
  exact this

end Psi

end ESGH

namespace ESGH

section Main

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ}
variable (E : (S2 M H × S2 M H) ≃ₗ[ℂ] V M H)
  (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : S2 M H),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((E (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H ℓ ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ))
  (hU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : S2 M H),
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ((E (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H q ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ))
  (hD : ∀ (d : (ZMod M)ˣ) (f g : S2 M H),
    ((E (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.diamondL M H ℂ d ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ))

include hT in
private theorem coe_Ψ_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (v : V M H) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((Ψ E (CuspForm.heckeTLinH 2 hℓ hℓM) v : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ) := by
  obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
  rw [Ψ_apply_E]
  exact hT ℓ hℓ hℓM f g

include hU in
private theorem coe_Ψ_U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (v : V M H) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ((Ψ E (CuspForm.heckeULinH 2 q) v : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H q ℂ (v : CohCarrier.H1 M H ℂ) := by
  obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
  rw [Ψ_apply_E]
  exact hU q hq hqM f g

include hD in
private theorem coe_Ψ_D (d : (ZMod M)ˣ) (v : V M H) :
    ((Ψ E (CuspForm.diamondLinH 2 d) v : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ) := by
  obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
  rw [Ψ_apply_E]
  exact hD d f g

include hT hU hD in
private theorem Gc_eq : Gc M H S = (Ψ E) '' (Gf M H S) := by
  ext T
  constructor
  · rintro (⟨ℓ, hℓ, hℓS, h⟩ | ⟨d, h⟩)
    · by_cases hℓM : ℓ ∣ M
      · refine ⟨CuspForm.heckeULinH 2 ℓ, Or.inr (Or.inl ⟨ℓ, hℓ, hℓM, rfl⟩), ?_⟩
        apply LinearMap.ext; intro v; apply Subtype.ext
        rw [coe_Ψ_U E hU ℓ hℓ hℓM, h v]
      · have hℓS' : ℓ ∉ S := by rcases hℓS with h' | h'; exacts [h', absurd h' hℓM]
        refine ⟨CuspForm.heckeTLinH 2 hℓ hℓM, Or.inl ⟨ℓ, hℓ, hℓM, hℓS', rfl⟩, ?_⟩
        apply LinearMap.ext; intro v; apply Subtype.ext
        rw [coe_Ψ_T E hT ℓ hℓ hℓM, h v]
    · refine ⟨CuspForm.diamondLinH 2 d, Or.inr (Or.inr ⟨d, rfl⟩), ?_⟩
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [coe_Ψ_D E hD d, h v]
  · rintro ⟨t, (⟨ℓ, hℓ, hℓM, hℓS, rfl⟩ | ⟨q, hq, hqM, rfl⟩ | ⟨d, rfl⟩), rfl⟩
    · exact Or.inl ⟨ℓ, hℓ, Or.inl hℓS, fun v => coe_Ψ_T E hT ℓ hℓ hℓM v⟩
    · exact Or.inl ⟨q, hq, Or.inr hqM, fun v => coe_Ψ_U E hU q hq hqM v⟩
    · exact Or.inr ⟨d, fun v => coe_Ψ_D E hD d v⟩

include hT hU hD in
private theorem A_eq_map : A M H S = (𝔸 M H S).map (Ψ E) := by
  rw [A_def, Gc_eq E hT hU hD, AlgHom.map_adjoin]

variable (b : Module.Basis (Fin 1) ↥(𝔸 M H S) (S2 M H))

private def f₀ : S2 M H := b 0

private theorem hf₀ (g : S2 M H) : ∃ T : ↥(𝔸 M H S), (T : Module.End ℂ (S2 M H)) (f₀ b) = g := by
  refine ⟨b.repr g 0, ?_⟩
  have := b.sum_repr g
  rw [Fin.sum_univ_one] at this
  exact this

private theorem eq_zero_of_apply_f₀ (t : ↥(𝔸 M H S)) (ht : (t : Module.End ℂ (S2 M H)) (f₀ b) = 0) : t = 0 := by
  have hli := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  exact hli (fun _ => t) (by rw [Fin.sum_univ_one]; exact ht) 0

private def κ : (↥(𝔸 M H S) × ↥(𝔸 M H S)) →ₗ[ℂ] V M H :=
  E.toLinearMap ∘ₗ
    (((LinearMap.applyₗ (f₀ b)).comp (𝔸 M H S).val.toLinearMap).prodMap
      ((LinearMap.applyₗ (f₀ b)).comp (𝔸 M H S).val.toLinearMap))

private theorem κ_apply (t : ↥(𝔸 M H S) × ↥(𝔸 M H S)) :
    κ E b t = E ((t.1 : Module.End ℂ (S2 M H)) (f₀ b), (t.2 : Module.End ℂ (S2 M H)) (f₀ b)) := rfl

private theorem κ_bijective : Function.Bijective (κ E b) := by
  constructor
  · intro s t h
    rw [κ_apply, κ_apply] at h
    have h' := E.injective h
    simp only [Prod.mk.injEq] at h'
    have h1 : s.1 - t.1 = 0 := eq_zero_of_apply_f₀ b _ (by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, h'.1, sub_self])
    have h2 : s.2 - t.2 = 0 := eq_zero_of_apply_f₀ b _ (by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, h'.2, sub_self])
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  · intro v
    obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
    obtain ⟨T₀, hT₀⟩ := hf₀ b f
    obtain ⟨T₁, hT₁⟩ := hf₀ b g
    exact ⟨(T₀, T₁), by rw [κ_apply, hT₀, hT₁]⟩

variable (hA : A M H S = (𝔸 M H S).map (Ψ E))

private def bv : Fin 2 → V M H := ![E (f₀ b, 0), E (0, f₀ b)]

include hA in
private theorem exists_of_mem_A (a : ↥(A M H S)) : ∃ t : ↥(𝔸 M H S), (a : Module.End ℂ (V M H)) = Ψ E t := by
  have ha : (a : Module.End ℂ (V M H)) ∈ (𝔸 M H S).map (Ψ E) := hA ▸ a.2
  obtain ⟨t, ht, hta⟩ := Subalgebra.mem_map.mp ha
  exact ⟨⟨t, ht⟩, hta.symm⟩

private theorem smul_bv_sum (t₀ t₁ : ↥(𝔸 M H S)) :
    (Ψ E t₀) (E (f₀ b, 0)) + (Ψ E t₁) (E (0, f₀ b)) =
      E ((t₀ : Module.End ℂ (S2 M H)) (f₀ b), (t₁ : Module.End ℂ (S2 M H)) (f₀ b)) := by
  rw [Ψ_apply_E, Ψ_apply_E, map_zero, map_zero, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

include hA in
private theorem linearIndependent_bv : LinearIndependent ↥(A M H S) (bv E b) := by
  refine (Fintype.linearIndependent_iff (ι := Fin 2) (R := ↥(A M H S)) (v := bv E b)).mpr ?_
  intro c hc
  obtain ⟨t₀, ht₀⟩ := exists_of_mem_A E hA (c 0)
  obtain ⟨t₁, ht₁⟩ := exists_of_mem_A E hA (c 1)
  rw [Fin.sum_univ_two] at hc
  change (c 0 : Module.End ℂ (V M H)) (E (f₀ b, 0)) + (c 1 : Module.End ℂ (V M H)) (E (0, f₀ b)) = 0 at hc
  rw [ht₀, ht₁, smul_bv_sum, ← κ_apply E b (t₀, t₁)] at hc
  have h0 : (t₀, t₁) = 0 := (κ_bijective E b).1 (hc.trans (map_zero _).symm)
  simp only [Prod.mk_eq_zero] at h0
  intro i
  fin_cases i
  · apply Subtype.ext; change (c 0 : Module.End ℂ (V M H)) = 0; rw [ht₀, h0.1]; exact map_zero _
  · apply Subtype.ext; change (c 1 : Module.End ℂ (V M H)) = 0; rw [ht₁, h0.2]; exact map_zero _

include hA in
private theorem span_bv : ⊤ ≤ Submodule.span ↥(A M H S) (Set.range (bv E b)) := by
  intro v _
  obtain ⟨⟨t₀, t₁⟩, rfl⟩ := (κ_bijective E b).2 v
  rw [κ_apply, ← smul_bv_sum]
  have hm0 : Ψ E t₀ ∈ A M H S := by rw [hA]; exact Subalgebra.mem_map.mpr ⟨_, t₀.2, rfl⟩
  have hm1 : Ψ E t₁ ∈ A M H S := by rw [hA]; exact Subalgebra.mem_map.mpr ⟨_, t₁.2, rfl⟩
  have e0 : (Ψ E t₀) (E (f₀ b, 0)) = (⟨Ψ E t₀, hm0⟩ : ↥(A M H S)) • bv E b 0 := rfl
  have e1 : (Ψ E t₁) (E (0, f₀ b)) = (⟨Ψ E t₁, hm1⟩ : ↥(A M H S)) • bv E b 1 := rfl
  rw [e0, e1]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

private def basisA : Module.Basis (Fin 2) ↥(A M H S) (V M H) :=
  Module.Basis.mk (linearIndependent_bv E b hA) (span_bv E b hA)

private def eig𝔸 (χ' : ↥(𝔸 M H S) → ℂ) : Submodule ℂ ↥(𝔸 M H S) where
  carrier := {x | ∀ t : ↥(𝔸 M H S), t * x = χ' t • x}
  zero_mem' t := by simp
  add_mem' {x y} hx hy t := by rw [mul_add, hx t, hy t, smul_add]
  smul_mem' c x hx t := by rw [mul_smul_comm, hx t, smul_comm]

include b in
private theorem eig𝔸_line (χ' : ↥(𝔸 M H S) →ₐ[ℂ] ℂ)
    (hone : Module.finrank ℂ ↥(⨅ a : ↥(𝔸 M H S),
      Module.End.eigenspace (a : Module.End ℂ (S2 M H)) (χ' a)) = 1) :
    ∃ x₀ : ↥(𝔸 M H S), x₀ ∈ eig𝔸 (S := S) χ' ∧ x₀ ≠ 0 ∧
      ∀ y ∈ eig𝔸 (S := S) χ', ∃ c : ℂ, y = c • x₀ := by
  set W : Submodule ℂ (S2 M H) := ⨅ a : ↥(𝔸 M H S),
    Module.End.eigenspace (a : Module.End ℂ (S2 M H)) (χ' a) with hW
  have hmemW : ∀ w : S2 M H, w ∈ W ↔ ∀ a : ↥(𝔸 M H S), (a : Module.End ℂ (S2 M H)) w = χ' a • w := by
    intro w
    simp only [hW, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  haveI : Module.Finite ℂ ↥W := Module.finite_of_finrank_eq_succ hone
  obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w₀ : S2 M H, w₀ ∈ W ∧ w₀ ≠ 0 := by
    have : 0 < Module.finrank ℂ ↥W := by rw [hone]; exact one_pos
    obtain ⟨⟨w, hw⟩, hne⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp this
    exact ⟨w, hw, fun h => hne (Subtype.ext h)⟩
  have hline : ∀ w ∈ W, ∃ c : ℂ, w = c • w₀ := by
    intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w₀, hw₀W⟩ : ↥W)
      (fun h => hw₀ (congrArg Subtype.val h))).mp hone ⟨w, hw⟩
    exact ⟨c, by have := congrArg Subtype.val hc; simpa using this.symm⟩
  obtain ⟨x₀, hx₀⟩ := hf₀ b w₀
  have hx₀mem : x₀ ∈ eig𝔸 (S := S) χ' := by
    intro t
    apply sub_eq_zero.mp
    apply eq_zero_of_apply_f₀ b
    rw [Subalgebra.coe_sub, LinearMap.sub_apply, Subalgebra.coe_mul, Module.End.mul_apply, hx₀,
      Subalgebra.coe_smul, LinearMap.smul_apply, hx₀, (hmemW w₀).mp hw₀W t, sub_self]
  have hx₀ne : x₀ ≠ 0 := by
    intro h; apply hw₀; rw [← hx₀, h]; rfl
  refine ⟨x₀, hx₀mem, hx₀ne, fun y hy => ?_⟩
  have hyW : (y : Module.End ℂ (S2 M H)) (f₀ b) ∈ W := by
    rw [hmemW]
    intro a
    rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, hy a, Subalgebra.coe_smul, LinearMap.smul_apply]
  obtain ⟨c, hc⟩ := hline _ hyW
  refine ⟨c, ?_⟩
  apply sub_eq_zero.mp
  apply eq_zero_of_apply_f₀ b
  rw [Subalgebra.coe_sub, LinearMap.sub_apply, hc, Subalgebra.coe_smul, LinearMap.smul_apply, hx₀, sub_self]

include b hA in
private theorem finrank_eigenspace_eq_two (χ : ↥(A M H S) →ₐ[ℂ] ℂ) (χ' : ↥(𝔸 M H S) → ℂ)
    (hχ' : ∀ t : ↥(𝔸 M H S), χ' t = χ ⟨Ψ E t, hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩⟩)
    (x₀ : ↥(𝔸 M H S)) (hx₀ : x₀ ∈ eig𝔸 (S := S) χ') (hx₀ne : x₀ ≠ 0)
    (hline : ∀ y ∈ eig𝔸 (S := S) χ', ∃ c : ℂ, y = c • x₀) :
    Module.finrank ℂ ↥(⨅ a : ↥(A M H S), Module.End.eigenspace (a : Module.End ℂ (V M H)) (χ a)) = 2 := by
  set Eχ : Submodule ℂ (V M H) := ⨅ a : ↥(A M H S), Module.End.eigenspace (a : Module.End ℂ (V M H)) (χ a)
  have hmem : ∀ t : ↥(𝔸 M H S) × ↥(𝔸 M H S),
      κ E b t ∈ Eχ ↔ t.1 ∈ eig𝔸 (S := S) χ' ∧ t.2 ∈ eig𝔸 (S := S) χ' := by
    intro t
    simp only [Eχ, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    constructor
    · intro h
      have key : ∀ s : ↥(𝔸 M H S), (s * t.1, s * t.2) = (χ' s • t.1, χ' s • t.2) := by
        intro s
        have hs := h ⟨Ψ E s, hA ▸ Subalgebra.mem_map.mpr ⟨_, s.2, rfl⟩⟩
        change Ψ E s (κ E b t) = _ at hs
        rw [κ_apply, Ψ_apply_E, ← hχ'] at hs
        apply (κ_bijective E b).1
        rw [κ_apply, κ_apply]
        simp only [Subalgebra.coe_mul, Module.End.mul_apply, Subalgebra.coe_smul, LinearMap.smul_apply]
          at hs ⊢
        rw [← Prod.smul_mk, map_smul]
        exact hs
      exact ⟨fun s => (Prod.ext_iff.mp (key s)).1, fun s => (Prod.ext_iff.mp (key s)).2⟩
    · rintro ⟨h1, h2⟩ a
      obtain ⟨s, hs⟩ := exists_of_mem_A E hA a
      have has : a = ⟨Ψ E s, hA ▸ Subalgebra.mem_map.mpr ⟨_, s.2, rfl⟩⟩ := Subtype.ext hs
      rw [has, ← hχ']
      change Ψ E s (κ E b t) = χ' s • κ E b t
      rw [κ_apply, Ψ_apply_E]
      have e1 : (s : Module.End ℂ (S2 M H)) ((t.1 : Module.End ℂ (S2 M H)) (f₀ b)) =
          χ' s • (t.1 : Module.End ℂ (S2 M H)) (f₀ b) := by
        rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, h1 s, Subalgebra.coe_smul, LinearMap.smul_apply]
      have e2 : (s : Module.End ℂ (S2 M H)) ((t.2 : Module.End ℂ (S2 M H)) (f₀ b)) =
          χ' s • (t.2 : Module.End ℂ (S2 M H)) (f₀ b) := by
        rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, h2 s, Subalgebra.coe_smul, LinearMap.smul_apply]
      rw [e1, e2, ← Prod.smul_mk, map_smul]
  have hxf : (x₀ : Module.End ℂ (S2 M H)) (f₀ b) ≠ 0 := fun h => hx₀ne (eq_zero_of_apply_f₀ b x₀ h)
  let φ : (ℂ × ℂ) →ₗ[ℂ] ↥Eχ :=
    { toFun := fun c => ⟨κ E b (c.1 • x₀, c.2 • x₀), (hmem _).mpr
        ⟨Submodule.smul_mem _ _ hx₀, Submodule.smul_mem _ _ hx₀⟩⟩
      map_add' := fun c d => by
        apply Subtype.ext
        change κ E b ((c.1 + d.1) • x₀, (c.2 + d.2) • x₀) =
          κ E b (c.1 • x₀, c.2 • x₀) + κ E b (d.1 • x₀, d.2 • x₀)
        rw [← map_add, Prod.mk_add_mk, ← add_smul, ← add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        change κ E b ((r * c.1) • x₀, (r * c.2) • x₀) = r • κ E b (c.1 • x₀, c.2 • x₀)
        rw [← map_smul, Prod.smul_mk, smul_smul, smul_smul] }
  have hφ : Function.Bijective φ := by
    constructor
    · intro c d h
      have h' := congrArg (fun z : ↥Eχ => (z : V M H)) h
      change κ E b _ = κ E b _ at h'
      rw [κ_apply, κ_apply] at h'
      have h'' := E.injective h'
      simp only [Prod.mk.injEq, Subalgebra.coe_smul, LinearMap.smul_apply] at h''
      obtain ⟨ha, hb⟩ := h''
      have ha' : (c.1 - d.1) • (x₀ : Module.End ℂ (S2 M H)) (f₀ b) = 0 := by rw [sub_smul, ha, sub_self]
      have hb' : (c.2 - d.2) • (x₀ : Module.End ℂ (S2 M H)) (f₀ b) = 0 := by rw [sub_smul, hb, sub_self]
      rw [smul_eq_zero] at ha' hb'
      exact Prod.ext (sub_eq_zero.mp (ha'.resolve_right hxf)) (sub_eq_zero.mp (hb'.resolve_right hxf))
    · rintro ⟨v, hv⟩
      obtain ⟨t, rfl⟩ := (κ_bijective E b).2 v
      obtain ⟨h1, h2⟩ := (hmem t).mp hv
      obtain ⟨a, ha⟩ := hline t.1 h1
      obtain ⟨b', hb'⟩ := hline t.2 h2
      refine ⟨(a, b'), Subtype.ext ?_⟩
      change κ E b (a • x₀, b' • x₀) = κ E b t
      rw [← ha, ← hb']
  rw [← (LinearEquiv.ofBijective φ hφ).finrank_eq, Module.finrank_prod, Module.finrank_self]

end Main

private def mkE {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (ES : (S2 M H × S2 M H) →ₗ[ℂ] CohCarrier.H1 M H ℂ) (hinj : Function.Injective ES)
    (hrange : LinearMap.range ES = parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) :
    (S2 M H × S2 M H) ≃ₗ[ℂ] V M H :=
  LinearEquiv.ofBijective (ES.codRestrict _ (fun fg => hrange ▸ LinearMap.mem_range_self ES fg))
    ⟨fun x y h => hinj (congrArg Subtype.val h), by
      rintro ⟨v, hv⟩
      rw [← hrange] at hv
      obtain ⟨fg, rfl⟩ := hv
      exact ⟨fg, rfl⟩⟩

private theorem coe_mkE {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (ES : (S2 M H × S2 M H) →ₗ[ℂ] CohCarrier.H1 M H ℂ) (hinj : Function.Injective ES)
    (hrange : LinearMap.range ES = parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) (fg : S2 M H × S2 M H) :
    ((mkE ES hinj hrange fg : V M H) : CohCarrier.H1 M H ℂ) = ES fg := rfl

private theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 2) ↥(A M H S) (V M H)) ∧
    ∀ χ : ↥(A M H S) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(A M H S), Module.End.eigenspace (a : Module.End ℂ (V M H)) (χ a)) = 2 := by
  obtain ⟨J, ES, -, -, hinj, hrange, hT', hU', hD'⟩ := CohCarrier.exists_eichlerShimura_H1_gammaH M H
  have hEcoe := coe_mkE ES hinj hrange
  generalize hE : mkE ES hinj hrange = E at hEcoe
  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : S2 M H),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ((E (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) : V M H) : CohCarrier.H1 M H ℂ) =
        CohCarrier.heckeT M H ℓ ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ) := by
    intro ℓ hℓ hℓM f g; rw [hEcoe, hEcoe]; exact hT' ℓ hℓ hℓM f g
  have hU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : S2 M H),
      haveI : NeZero q := ⟨hq.ne_zero⟩
      ((E (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) : V M H) : CohCarrier.H1 M H ℂ) =
        CohCarrier.heckeT M H q ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ) := by
    intro q hq hqM f g; rw [hEcoe, hEcoe]; exact hU' q hq hqM f g
  have hD : ∀ (d : (ZMod M)ˣ) (f g : S2 M H),
      ((E (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) : V M H) : CohCarrier.H1 M H ℂ) =
        CohCarrier.diamondL M H ℂ d ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ) := by
    intro d f g; rw [hEcoe, hEcoe]; exact hD' d f g
  obtain ⟨⟨b⟩, hone⟩ := CuspForm.nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one M H S hSfin

  obtain ⟨hA⟩ : PLift (A M H S = (𝔸 M H S).map (Ψ E)) := ⟨A_eq_map E hT hU hD⟩
  refine ⟨Nonempty.intro (basisA (S := S) E b hA), fun χ => ?_⟩
  let ι : ↥(𝔸 M H S) →ₐ[ℂ] ↥(A M H S) :=
    ((Ψ E).comp (𝔸 M H S).val).codRestrict (A M H S)
      (fun t => hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩)
  let χ' : ↥(𝔸 M H S) →ₐ[ℂ] ℂ := χ.comp ι
  have hχ' : ∀ t : ↥(𝔸 M H S), χ' t = χ ⟨Ψ E t, hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩⟩ :=
    fun t => rfl
  obtain ⟨x₀, hx₀, hx₀ne, hline⟩ := eig𝔸_line b χ' (hone χ')
  exact finrank_eigenspace_eq_two E b hA χ χ' hχ' x₀ hx₀ hx₀ne hline

end ESGH

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))})
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}),
        Module.End.eigenspace (a : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) (χ a)) = 2 :=
  ESGH.main M H S hSfin

end
end S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two
end P2MW
export P2MW.S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two (solution)
