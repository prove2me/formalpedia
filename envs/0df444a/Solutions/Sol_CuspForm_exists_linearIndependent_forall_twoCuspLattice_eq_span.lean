-- Prove2me | solution 1 for CuspForm.exists_linearIndependent_forall_twoCuspLattice_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ebfecfd1-fe65-5e79-a2e9-725524b4e0d2

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Theorems.Thm_CuspForm_span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top
import Theorems.Thm_CuspForm_exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one"
p2m_attr_erase "simp" "Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false

open Module Submodule

namespace TwoCuspLatticeAlg

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def intSub (Φ : Set (Module.Dual ℂ V)) : Submodule ℤ V where
  carrier := {v | ∀ φ ∈ Φ, ∃ m : ℤ, φ v = (m : ℂ)}
  zero_mem' := fun φ _ => ⟨0, by simp⟩
  add_mem' := by
    intro v w hv hw φ hφ
    obtain ⟨m, hm⟩ := hv φ hφ
    obtain ⟨m', hm'⟩ := hw φ hφ
    exact ⟨m + m', by rw [map_add, hm, hm']; push_cast; ring⟩
  smul_mem' := by
    intro c v hv φ hφ
    obtain ⟨m, hm⟩ := hv φ hφ
    exact ⟨c * m, by rw [map_zsmul, hm, zsmul_eq_mul]; push_cast; ring⟩

theorem mem_intSub {Φ : Set (Module.Dual ℂ V)} {v : V} :
    v ∈ intSub Φ ↔ ∀ φ ∈ Φ, ∃ m : ℤ, φ v = (m : ℂ) := Iff.rfl

def subringSub (Φ : Set (Module.Dual ℂ V)) (A : Subring ℂ) : Submodule A V where
  carrier := {v | ∀ φ ∈ Φ, φ v ∈ A}
  zero_mem' := fun φ _ => by rw [map_zero]; exact A.zero_mem
  add_mem' := fun {v w} hv hw φ hφ => by rw [map_add]; exact A.add_mem (hv φ hφ) (hw φ hφ)
  smul_mem' := fun a {v} hv φ hφ => by
    rw [Subring.smul_def, map_smul, smul_eq_mul]; exact A.mul_mem a.2 (hv φ hφ)

theorem mem_subringSub {Φ : Set (Module.Dual ℂ V)} {A : Subring ℂ} {v : V} :
    v ∈ subringSub Φ A ↔ ∀ φ ∈ Φ, φ v ∈ A := Iff.rfl

def Separates (Φ : Set (Module.Dual ℂ V)) : Prop := ∀ v : V, (∀ φ ∈ Φ, φ v = 0) → v = 0

section FinDim

variable [FiniteDimensional ℂ V]

theorem span_eq_top_of_separates {Φ : Set (Module.Dual ℂ V)} (hΦ : Separates Φ) :
    span ℂ Φ = ⊤ :=
  Submodule.span_eq_top_of_ne_zero fun z hz => by
    by_contra! h
    exact hz (hΦ z h)

theorem exists_basis_mem {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {s : Set W} (hs : span ℂ s = ⊤) :
    ∃ v : Basis (Fin (finrank ℂ W)) ℂ W, ∀ k, v k ∈ s := by
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℂ s
  rw [hs] at hspan
  have hfin : b.Finite := hli.setFinite
  letI : Fintype b := hfin.fintype
  let B : Basis b ℂ W := Basis.mk hli (by rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan])
  have hcard : Fintype.card b = finrank ℂ W := (Module.finrank_eq_card_basis B).symm
  refine ⟨B.reindex (Fintype.equivFinOfCardEq hcard), fun k => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hbs (Subtype.coe_prop _)

theorem exists_dualBasis_mem {Φ : Set (Module.Dual ℂ V)} (hΦ : Separates Φ) :
    ∃ ψ : Basis (Fin (finrank ℂ V)) ℂ (Module.Dual ℂ V), ∀ j, ψ j ∈ Φ := by
  obtain ⟨ψ, hψ⟩ := exists_basis_mem (W := Module.Dual ℂ V) (span_eq_top_of_separates hΦ)
  have h : finrank ℂ (Module.Dual ℂ V) = finrank ℂ V := Subspace.dual_finrank_eq
  exact ⟨ψ.reindex (finCongr h), fun j => by rw [Basis.reindex_apply]; exact hψ _⟩

theorem exists_det_smul_coord_eq {Φ : Set (Module.Dual ℂ V)} (hΦ : Separates Φ)
    (v : Basis (Fin (finrank ℂ V)) ℂ V) (hv : ∀ k, v k ∈ intSub Φ) :
    ∃ (ψ : Fin (finrank ℂ V) → Module.Dual ℂ V) (P : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℤ),
      (∀ j, ψ j ∈ Φ) ∧ P.det ≠ 0 ∧
      ∀ w : V, (P.det : ℂ) • v.equivFun w =
        (P.adjugate.map (Int.castRingHom ℂ)).mulVec (fun j => ψ j w) := by
  obtain ⟨ψ, hψ⟩ := exists_dualBasis_mem hΦ

  have hint : ∀ j k, ∃ m : ℤ, ψ j (v k) = (m : ℂ) := fun j k => hv k (ψ j) (hψ j)
  choose P hP using hint
  let Pc : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ := fun j k => ψ j (v k)
  have hPc : (Matrix.of P).map (Int.castRingHom ℂ) = Pc := by
    ext j k; simp [Pc, hP]

  have hmul : ∀ w : V, Pc.mulVec (v.equivFun w) = fun j => ψ j w := by
    intro w
    ext j
    conv_rhs => rw [← v.sum_equivFun w]
    simp only [Matrix.mulVec, dotProduct, Pc, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hdet : Pc.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hPc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    set w : V := v.equivFun.symm c with hw
    have hcw : v.equivFun w = c := by rw [hw]; exact v.equivFun.apply_symm_apply c
    have hψw : ∀ j, ψ j w = 0 := by
      intro j
      have := congr_fun (hmul w) j
      rw [hcw, hPc0] at this
      exact this.symm
    have hall : ∀ φ : Module.Dual ℂ V, φ w = 0 := by
      intro φ
      have hmem : φ ∈ span ℂ (Set.range ψ) := by rw [ψ.span_eq]; exact mem_top
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨j, rfl⟩; exact hψw j
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro a x _ hx; simp [hx]
    have hw0 : w = 0 := hΦ w fun φ _ => hall φ
    apply hc
    rw [← hcw, hw0, map_zero]
  have hdetP : (Matrix.of P).det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hPc]
    have := RingHom.map_det (Int.castRingHom ℂ) (Matrix.of P)
    rw [h0, map_zero, RingHom.mapMatrix_apply] at this
    simpa using this.symm
  refine ⟨ψ, Matrix.of P, hψ, hdetP, fun w => ?_⟩
  have hadj : (Matrix.of P).adjugate.map (Int.castRingHom ℂ) = Pc.adjugate := by
    rw [← hPc]
    have := RingHom.map_adjugate (Int.castRingHom ℂ) (Matrix.of P)
    simpa [RingHom.mapMatrix_apply] using this
  have hdetc : ((Matrix.of P).det : ℂ) = Pc.det := by
    rw [← hPc]
    have := RingHom.map_det (Int.castRingHom ℂ) (Matrix.of P)
    simpa [RingHom.mapMatrix_apply] using this
  rw [hadj, hdetc, ← hmul w, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec]

omit [FiniteDimensional ℂ V] in

theorem mem_span_int_of_coord_eq_intCast (v : Basis (Fin (finrank ℂ V)) ℂ V) (w : V)
    (n : Fin (finrank ℂ V) → ℤ) (h : v.equivFun w = fun k => (n k : ℂ)) :
    w ∈ span ℤ (Set.range v) := by
  rw [← v.sum_equivFun w, h]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩)

theorem exists_common_denom {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ i, ∃ z : ℤ, (N : ℚ) * q i = z := by
  classical
  refine ⟨∏ i, ((q i).den : ℤ), ?_, fun i => ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (q i).den_nz
  · refine ⟨(∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ)) * (q i).num, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ((q j).den : ℤ)) (Finset.mem_univ i)]
    push_cast
    rw [mul_comm ((q i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]

theorem exists_smul_mem_span_int {Φ : Set (Module.Dual ℂ V)} (hΦ : Separates Φ)
    (v : Basis (Fin (finrank ℂ V)) ℂ V) (hv : ∀ k, v k ∈ intSub Φ) :
    ∃ D : ℤ, D ≠ 0 ∧ (∀ w ∈ intSub Φ, D • w ∈ span ℤ (Set.range v)) ∧
      ∀ w : V, (∀ φ ∈ Φ, ∃ r : ℚ, φ w = (r : ℂ)) → ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ span ℤ (Set.range v) := by
  obtain ⟨ψ, P, hψ, hD, hid⟩ := exists_det_smul_coord_eq hΦ v hv
  refine ⟨P.det, hD, fun w hw => ?_, fun w hw => ?_⟩
  · have hm : ∀ j, ∃ m : ℤ, ψ j w = (m : ℂ) := fun j => hw (ψ j) (hψ j)
    choose m hm using hm
    apply mem_span_int_of_coord_eq_intCast v _ (P.adjugate.mulVec m)
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, hid w]
    ext k
    rw [← eq_intCast (Int.castRingHom ℂ) (P.adjugate.mulVec m k), RingHom.map_mulVec]
    congr 1
    ext j
    simp [hm j]
  · have hr : ∀ j, ∃ r : ℚ, ψ j w = (r : ℂ) := fun j => hw (ψ j) (hψ j)
    choose r hr using hr
    obtain ⟨N, hN, hz⟩ := exists_common_denom r
    choose z hz using hz
    refine ⟨P.det * N, mul_ne_zero hD hN, ?_⟩
    apply mem_span_int_of_coord_eq_intCast v _ (P.adjugate.mulVec z)
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, Int.cast_mul, mul_comm, mul_smul, hid w,
      ← Matrix.mulVec_smul]
    ext k
    rw [← eq_intCast (Int.castRingHom ℂ) (P.adjugate.mulVec z k), RingHom.map_mulVec]
    congr 1
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, hr j, eq_intCast]
    have := congrArg (fun q : ℚ => (q : ℂ)) (hz j)
    push_cast at this
    exact this

theorem exists_basis_intSub {Φ : Set (Module.Dual ℂ V)} (hΦ : Separates Φ)
    (hsp : span ℂ (intSub Φ : Set V) = ⊤) :
    ∃ b : Fin (finrank ℂ V) → V, LinearIndependent ℂ b ∧ span ℂ (Set.range b) = ⊤ ∧
      ∀ w : V, w ∈ intSub Φ ↔ ∃ n : Fin (finrank ℂ V) → ℤ, w = ∑ i, n i • b i := by
  obtain ⟨v, hv⟩ := exists_basis_mem (W := V) hsp
  obtain ⟨D, hD, hDL, -⟩ := exists_smul_mem_span_int hΦ v hv
  set L : Submodule ℤ V := intSub Φ
  set L₀ : Submodule ℤ V := span ℤ (Set.range v) with hL₀def
  have hL₀L : L₀ ≤ L := span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hv k)
  haveI : IsAddTorsionFree V := .of_isTorsionFree ℂ V

  have hDL' : ∀ x ∈ L, (D • (LinearMap.id : V →ₗ[ℤ] V)) x ∈ L₀ := fun x hx => hDL x hx
  let μ : L →ₗ[ℤ] L₀ := (D • (LinearMap.id : V →ₗ[ℤ] V)).restrict hDL'
  have hμ : Function.Injective μ := by
    intro x y hxy
    apply Subtype.ext
    have : D • (x : V) = D • (y : V) := congrArg Subtype.val hxy
    exact (smul_right_inj hD).mp this
  haveI : Module.Finite ℤ L₀ := Module.Finite.span_of_finite ℤ (Set.finite_range v)
  haveI : Module.Finite ℤ L := Module.Finite.of_injective μ hμ
  have hvℤ : LinearIndependent ℤ v := v.linearIndependent.restrict_scalars' ℤ
  have hrk₀ : finrank ℤ L₀ = finrank ℂ V := by
    rw [hL₀def, finrank_span_eq_card hvℤ, Fintype.card_fin]
  have h1 : finrank ℤ L ≤ finrank ℤ L₀ := LinearMap.finrank_le_finrank_of_injective hμ
  have h2 : finrank ℤ L₀ ≤ finrank ℤ L :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hL₀L)
  have hrk : finrank ℤ L = finrank ℂ V := le_antisymm (h1.trans hrk₀.le) (hrk₀.ge.trans h2)
  let β : Basis (Fin (finrank ℂ V)) ℤ L := (Module.finBasis ℤ L).reindex (finCongr hrk)
  let b : Fin (finrank ℂ V) → V := fun i => (β i : V)
  have hbL : ∀ i, b i ∈ L := fun i => (β i).2

  have hmem : ∀ w : V, w ∈ L ↔ ∃ n : Fin (finrank ℂ V) → ℤ, w = ∑ i, n i • b i := by
    intro w
    constructor
    · intro hw
      refine ⟨β.equivFun ⟨w, hw⟩, ?_⟩
      have h := congrArg Subtype.val (β.sum_equivFun ⟨w, hw⟩)
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul] at h
      exact h.symm
    · rintro ⟨n, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbL i)

  have hspan : span ℂ (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← v.span_eq, span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨n, hn⟩ := (hmem (v k)).mp (hv k)
    rw [hn]
    exact Submodule.sum_mem _ fun i _ => zsmul_mem (subset_span ⟨i, rfl⟩ : b i ∈ span ℂ (Set.range b)) _
  have hli : LinearIndependent ℂ b :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (Fintype.card_fin _)
  exact ⟨b, hli, hspan, hmem⟩

theorem character_apply_eq_coe_sum {g : ℕ} (χ : (Fin g → ℤ) →+ AddCircle (1 : ℚ)) (x : Fin g → ℚ)
    (hx : ∀ i, ((x i : ℚ) : AddCircle (1 : ℚ)) = χ (Pi.single i 1)) (m : Fin g → ℤ) :
    χ m = (((∑ i, (m i : ℚ) * x i : ℚ)) : AddCircle (1 : ℚ)) := by
  have hm : m = ∑ i, m i • (Pi.single i (1 : ℤ) : Fin g → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hm]
  rw [map_sum]
  simp only [map_zsmul, ← hx]
  rw [QuotientAddGroup.mk_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]

theorem exists_basis_forall_subringSub_eq {Φ : Set (Module.Dual ℂ V)} (hΦ : Separates Φ)
    (hsp : span ℂ (intSub Φ : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Fin n → V), LinearIndependent ℂ b ∧ span ℂ (Set.range b) = ⊤ ∧
      ∀ A : Subring ℂ, subringSub Φ A = span A (Set.range b) := by
  obtain ⟨b, hli, hspan, hmem⟩ := exists_basis_intSub hΦ hsp
  refine ⟨finrank ℂ V, b, hli, hspan, fun A => ?_⟩
  let bB : Basis (Fin (finrank ℂ V)) ℂ V := Basis.mk hli hspan.ge
  have hbB : ∀ i, bB i = b i := fun i => by simp [bB]
  have hbint : ∀ i, b i ∈ intSub Φ := fun i =>
    (hmem (b i)).mpr ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  apply le_antisymm
  swap
  ·
    rw [span_le]
    rintro _ ⟨i, rfl⟩ φ hφ
    obtain ⟨m, hm⟩ := hbint i φ hφ
    rw [hm]
    exact intCast_mem A m
  · intro w hw

    have hwc : w = ∑ k, bB.equivFun w k • b k := by
      conv_lhs => rw [← bB.sum_equivFun w]
      simp only [hbB]
    set c : Fin (finrank ℂ V) → ℂ := bB.equivFun w with hc

    have hd : ∀ (i : Fin (finrank ℂ V)) (φ : Φ), ∃ m : ℤ, (φ : Module.Dual ℂ V) (b i) = (m : ℂ) :=
      fun i φ => hbint i φ φ.2
    choose d hdφ using hd
    let dv : Φ → (Fin (finrank ℂ V) → ℤ) := fun φ i => d i φ
    let Dmod : Submodule ℤ (Fin (finrank ℂ V) → ℤ) := span ℤ (Set.range dv)

    have htop : Dmod = ⊤ := by
      by_contra hne
      obtain ⟨y, hy⟩ : ∃ y, y ∉ Dmod := by
        by_contra! h
        exact hne (eq_top_iff'.mpr h)
      have hy0 : Dmod.mkQ y ≠ 0 := by
        rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hy0
      let χ' : (Fin (finrank ℂ V) → ℤ) →+ AddCircle (1 : ℚ) := (χ : _ →+ _).comp Dmod.mkQ.toAddMonoidHom
      have hχ' : ∀ m, χ' m = χ (Dmod.mkQ m) := fun m => rfl
      have hx : ∀ i, ∃ x : ℚ, ((x : ℚ) : AddCircle (1 : ℚ)) = χ' (Pi.single i 1) :=
        fun i => QuotientAddGroup.mk_surjective _
      choose x hx using hx
      have heval := character_apply_eq_coe_sum χ' x hx

      have hint : ∀ φ : Φ, ∃ nφ : ℤ, (∑ i, (dv φ i : ℚ) * x i) = nφ := by
        intro φ
        have h0 : χ' (dv φ) = 0 := by
          rw [hχ', Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Dmod).mpr (subset_span ⟨φ, rfl⟩),
            map_zero]
        rw [heval] at h0
        obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp h0
        exact ⟨n, by rw [← hn, zsmul_eq_mul, mul_one]⟩
      choose nφ hnφ using hint

      let u : V := ∑ i, ((x i : ℚ) : ℂ) • b i
      have hu : u ∈ intSub Φ := by
        intro φ hφ
        refine ⟨nφ ⟨φ, hφ⟩, ?_⟩
        have : φ u = ((∑ i, (dv ⟨φ, hφ⟩ i : ℚ) * x i : ℚ) : ℂ) := by
          simp only [u, map_sum, map_smul, smul_eq_mul]
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hdφ i ⟨φ, hφ⟩]
          ring
        rw [this, hnφ ⟨φ, hφ⟩]
        push_cast
        rfl
      obtain ⟨m, hm⟩ := (hmem u).mp hu
      have hxm : ∀ i, x i = m i := by
        intro i
        have h1 : bB.equivFun u = fun i => ((x i : ℚ) : ℂ) := by
          apply bB.equivFun.symm.injective
          rw [LinearEquiv.symm_apply_apply, Basis.equivFun_symm_apply]
          simp only [hbB, u]
        have h2 : bB.equivFun u = fun i => ((m i : ℤ) : ℂ) := by
          apply bB.equivFun.symm.injective
          rw [LinearEquiv.symm_apply_apply, Basis.equivFun_symm_apply]
          simp only [hbB]
          rw [hm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Int.cast_smul_eq_zsmul]
        have := congr_fun (h1.symm.trans h2) i
        have h3 : ((x i : ℚ) : ℂ) = ((m i : ℚ) : ℂ) := by rw [this]; push_cast; rfl
        exact_mod_cast h3
      apply hχ
      rw [← hχ', heval]
      refine (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨∑ i, y i * m i, ?_⟩
      rw [zsmul_eq_mul, mul_one]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [hxm i]

    have hcA : ∀ i, c i ∈ A := by
      intro i
      have hei : (Pi.single i (1 : ℤ) : Fin (finrank ℂ V) → ℤ) ∈ Dmod := by rw [htop]; exact mem_top
      have key : ∀ y ∈ Dmod, (∑ k, (y k : ℂ) * c k) ∈ A := by
        intro y hy
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨φ, rfl⟩
          have : (∑ k, (dv φ k : ℂ) * c k) = (φ : Module.Dual ℂ V) w := by
            rw [hwc, map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [map_smul, smul_eq_mul, hdφ k φ, mul_comm]
          rw [this]
          exact hw φ φ.2
        · simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
          exact A.zero_mem
        · intro y₁ y₂ _ _ h₁ h₂
          have : (∑ k, ((y₁ + y₂) k : ℂ) * c k) = (∑ k, (y₁ k : ℂ) * c k) + ∑ k, (y₂ k : ℂ) * c k := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [Pi.add_apply, Int.cast_add]; ring
          rw [this]; exact A.add_mem h₁ h₂
        · intro a y _ h
          have : (∑ k, ((a • y) k : ℂ) * c k) = (a : ℂ) * ∑ k, (y k : ℂ) * c k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]; ring
          rw [this]; exact A.mul_mem (intCast_mem A a) h
      have := key _ hei
      simpa [Pi.single_apply] using this
    rw [hwc]
    refine Submodule.sum_mem _ fun k _ => ?_
    have : c k • b k = (⟨c k, hcA k⟩ : A) • b k := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩)

end FinDim

end TwoCuspLatticeAlg

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open CongruenceSubgroup CohCarrier UpperHalfPlane

namespace TwoCuspLatticeConc

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_zpow_mem_GammaH (s : ℤ) : ModularGroup.T ^ s ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  have hT0 : ModularGroup.T ^ s ∈ Gamma0 M := by
    rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
  refine ⟨hT0, ?_⟩
  have : gamma0Units M ⟨ModularGroup.T ^ s, hT0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show (((ModularGroup.T ^ s) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [ModularGroup.coe_T_zpow]; simp
  rw [this]
  exact one_mem H

theorem T_mem_GammaH : ModularGroup.T ∈ GammaH M H := by
  simpa using T_zpow_mem_GammaH (M := M) (H := H) 1

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_GammaH]
  exact AddSubgroup.mem_zmultiples _

theorem mem_GammaH_of_unitsMap_eq {R : ℕ} (hR : R ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap hR u = 1 → u ∈ H)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (h : ZMod.unitsMap hR (gamma0Units M ⟨δ, hδ⟩) = ZMod.unitsMap hR u) :
    δ ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  refine ⟨hδ, ?_⟩
  have hker : gamma0Units M ⟨δ, hδ⟩ * u⁻¹ ∈ H :=
    hHp _ (by rw [map_mul, map_inv, h, mul_inv_cancel])
  simpa using H.mul_mem hker hu

theorem hHp_transfer {R₁ R₂ : ℕ} (h₁ : R₁ ∣ M) (h₂ : R₂ ∣ M) (heq : R₁ = R₂)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap h₁ u = 1 → u ∈ H) :
    ∀ u : (ZMod M)ˣ, ZMod.unitsMap h₂ u = 1 → u ∈ H := by
  subst heq
  exact hHp

theorem Gamma0_le_of_dvd {R : ℕ} (hR : R ∣ M) : Gamma0 M ≤ Gamma0 R := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have := congrArg (ZMod.castHom hR (ZMod R)) hγ
  rw [map_zero, map_intCast] at this
  exact this

theorem unitsMap_gamma0Units {R : ℕ} [NeZero R] (hR : R ∣ M) (σ : Gamma0 M) :
    ZMod.unitsMap hR (gamma0Units M σ) = gamma0Units R ⟨σ, Gamma0_le_of_dvd hR σ.2⟩ := by
  ext
  rw [ZMod.unitsMap_val, val_gamma0Units, val_gamma0Units]
  show ((((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M).cast : ZMod R) = (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod R)
  rw [ZMod.cast_intCast hR]

end Group

section Forms

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ}

def restrictCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) : CuspForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono h)

def slashCusp {Γ₁ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₁ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : CuspForm Γ₁ k) : CuspForm Γ₁ k :=
  restrictCusp hg (CuspForm.translate f g)

@[scoped simp] theorem coe_slashCusp {Γ₁ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₁ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : CuspForm Γ₁ k) :
    ⇑(slashCusp g hg f) = ⇑f ∣[k] g := rfl

def coef (n : ℕ) : CuspForm (Γ M H) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := by
    show PowerSeries.coeff n (qExpansion 1 ⇑(f + g)) =
      PowerSeries.coeff n (qExpansion 1 ⇑f) + PowerSeries.coeff n (qExpansion 1 ⇑g)
    rw [CuspForm.coe_add, qExpansion_add
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods)
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods), map_add]
  map_smul' c f := by
    show PowerSeries.coeff n (qExpansion 1 ⇑(c • f)) = c • PowerSeries.coeff n (qExpansion 1 ⇑f)
    rw [CuspForm.IsGLPos.coe_smul, qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods), map_smul]

theorem coef_apply (n : ℕ) (f : CuspForm (Γ M H) k) : coef n f = ModularFormClass.qCoeff (⇑f) n := rfl

theorem eq_zero_of_forall_coef_eq_zero (f : CuspForm (Γ M H) k) (h : ∀ n, coef n f = 0) : f = 0 := by
  have hq : qExpansion 1 (⇑f) = 0 := by
    ext n
    rw [map_zero]
    exact h n
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods
  haveI : Fact (IsCusp OnePoint.infty (Γ M H)) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods⟩
  have hzero := (qExpansion_eq_zero_iff one_pos hper (CuspFormClass.holo f)
    (ModularFormClass.bdd_at_infty f)).mp hq
  exact DFunLike.coe_injective (hzero.trans CuspForm.coe_zero.symm)

end Forms

section AL

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} (W : ModularForm.AtkinLehnerDatum M p)

omit [NeZero M] in

theorem R_dvd : W.R ∣ M := Dvd.intro_left p W.hM.symm

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem exists_alGL_mul_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
        = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) := by
  obtain ⟨δ, hδ, hW⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq W hγ
  refine ⟨δ, hδ, hW, ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast W.q_pos.ne'

  have h11 := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hW
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.alGL_coe,
    mapGL_coe_eq, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] at h11
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, eq_intCast] at h11
  have hZ : (p : ℤ) * (W.R : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (p : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * W.b + (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (p : ℤ) := by
    exact_mod_cast h11
  have hMδ : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hδ
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨s, hs⟩ := hMδ
  rw [hs, W.hM_int] at hZ
  have hcancel : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 + (W.R : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 - s * W.b) := by
    have : (p : ℤ) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
        - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 + (W.R : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 - s * W.b))) = 0 := by
      linear_combination -hZ
    have h2 := (mul_eq_zero.mp this).resolve_left hp0
    linear_combination h2
  rw [hcancel]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]

theorem le_conj_alGL (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H) :
    Γ M H ≤ ConjAct.toConjAct W.alGL⁻¹ • Γ M H := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  obtain ⟨δ, hδ, hW, hcong⟩ := exists_alGL_mul_eq W hγ0
  refine ⟨δ, ?_, ?_⟩
  · haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
    refine mem_GammaH_of_unitsMap_eq (R_dvd W) hHp hδ hγH ?_
    rw [unitsMap_gamma0Units, unitsMap_gamma0Units]
    ext
    rw [val_gamma0Units, val_gamma0Units]
    exact hcong
  · show (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ)
      = W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ * W.alGL⁻¹
    rw [hW, mul_inv_cancel_right]

def alLin (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H) (k : ℤ) :
    CuspForm (Γ M H) k →ₗ[ℂ] CuspForm (Γ M H) k where
  toFun f := slashCusp W.alGL (le_conj_alGL W hHp) f
  map_add' f g := DFunLike.coe_injective <| by
    show ⇑(f + g) ∣[k] W.alGL = ⇑f ∣[k] W.alGL + ⇑g ∣[k] W.alGL
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show ⇑(c • f) ∣[k] W.alGL = c • (⇑f ∣[k] W.alGL)
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.smul_slash, ModularForm.AtkinLehnerDatum.σ_alGL_apply]

@[scoped simp] theorem coe_alLin (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H) (k : ℤ)
    (f : CuspForm (Γ M H) k) : ⇑(alLin W hHp k f) = ModularForm.alSlash W k ⇑f := rfl

theorem alGL_eq_T_zpow_mul (W' : ModularForm.AtkinLehnerDatum M p) :
    W'.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (W.a * W'.b - W'.a * W.b)) * W.alGL := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast W.q_pos.ne'
  have hR : W'.R = W.R := by
    have h := W.hM.symm.trans W'.hM
    exact (Nat.eq_of_mul_eq_mul_left W.q_pos h).symm

  have hsR : (W.a * W'.b - W'.a * W.b) * (W.R : ℤ) = W'.a - W.a := by
    have h1 := W.bezout; have h2 := W'.bezout; rw [hR] at h2
    linear_combination W'.a * h1 - W.a * h2
  have hsp : (W.a * W'.b - W'.a * W.b) * (p : ℤ) = W'.b - W.b := by
    have h1 := W.bezout; have h2 := W'.bezout; rw [hR] at h2
    linear_combination W'.b * h1 - W.b * h2
  apply Units.ext
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.AtkinLehnerDatum.alGL_coe,
    mapGL_coe_eq, ModularGroup.coe_T_zpow, ← Matrix.map_mul]
  congr 1
  rw [ModularForm.AtkinLehnerDatum.mat, ModularForm.AtkinLehnerDatum.mat, hR]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -(p : ℤ) * hsR
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -hsp
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] in

theorem alSlash_eq_alSlash [NeZero M] (W' : ModularForm.AtkinLehnerDatum M p) (k : ℤ)
    (f : CuspForm (Γ M H) k) :
    ModularForm.alSlash W' k ⇑f = ModularForm.alSlash W k ⇑f := by
  rw [ModularForm.alSlash_def, ModularForm.alSlash_def, alGL_eq_T_zpow_mul W W', SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (T_zpow_mem_GammaH _))]

end AL

section Assembly

open TwoCuspLatticeAlg

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ}

def KerHyp (M : ℕ) (H : Subgroup (ZMod M)ˣ) (p : ℕ) : Prop :=
  ∀ (W : ModularForm.AtkinLehnerDatum M p) (u : (ZMod M)ˣ), ZMod.unitsMap (R_dvd W) u = 1 → u ∈ H

scoped instance : FiniteDimensional ℂ (CuspForm (Γ M H) 2) := CuspForm.finiteDimensional_of_isArithmetic (Γ M H) 2

def PhiOne (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : Set (Module.Dual ℂ (CuspForm (Γ M H) 2)) :=
  {φ | ∃ t ∈ CuspForm.heckeRingH M H 2, ∃ n : ℕ, φ = (coef n).comp t}

def PhiTwo (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) (hH : KerHyp M H p) :
    Set (Module.Dual ℂ (CuspForm (Γ M H) 2)) :=
  {φ | ∃ t ∈ CuspForm.heckeRingH M H 2, ∃ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
    φ = (coef n).comp ((alLin W (hH W) 2).comp t)}

def PhiZero (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : Set (Module.Dual ℂ (CuspForm (Γ M H) 2)) :=
  Set.range fun n : ℕ => (coef n : Module.Dual ℂ (CuspForm (Γ M H) 2))

theorem coef_comp_one_mem_PhiOne (n : ℕ) :
    (coef n).comp (1 : CuspForm (Γ M H) 2 →ₗ[ℂ] CuspForm (Γ M H) 2) ∈ PhiOne M H :=
  ⟨1, Subring.one_mem _, n, rfl⟩

theorem separates_PhiZero : Separates (PhiZero M H) := fun f hf =>
  eq_zero_of_forall_coef_eq_zero f fun n => hf _ ⟨n, rfl⟩

theorem separates_PhiOne : Separates (PhiOne M H) := fun f hf =>
  eq_zero_of_forall_coef_eq_zero f fun n => by
    have := hf _ (coef_comp_one_mem_PhiOne n)
    simpa using this

theorem separates_union (hH : KerHyp M H p) : Separates (PhiOne M H ∪ PhiTwo M H p hH) := fun f hf =>
  separates_PhiOne f fun φ hφ => hf φ (Or.inl hφ)

theorem mem_intSub_PhiOne_iff (f : CuspForm (Γ M H) 2) :
    f ∈ intSub (PhiOne M H) ↔
      ∀ t ∈ CuspForm.heckeRingH M H 2, ∀ n : ℕ, ∃ a : ℤ, ModularFormClass.qCoeff (⇑(t f)) n = (a : ℂ) := by
  constructor
  · intro hf t ht n
    exact hf _ ⟨t, ht, n, rfl⟩
  · rintro hf φ ⟨t, ht, n, rfl⟩
    exact hf t ht n

theorem heckeRingH_mem_intSub_PhiOne {t : CuspForm (Γ M H) 2 →ₗ[ℂ] CuspForm (Γ M H) 2}
    (ht : t ∈ CuspForm.heckeRingH M H 2) {f : CuspForm (Γ M H) 2} (hf : f ∈ intSub (PhiOne M H)) :
    t f ∈ intSub (PhiOne M H) := by
  rw [mem_intSub_PhiOne_iff] at hf ⊢
  intro t' ht' n
  exact hf (t' * t) ((CuspForm.heckeRingH M H 2).mul_mem ht' ht) n

theorem span_intSub_PhiOne_eq_top :
    Submodule.span ℂ (intSub (PhiOne M H) : Set (CuspForm (Γ M H) 2)) = ⊤ := by
  rw [eq_top_iff, ← CuspForm.span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top M H]
  refine Submodule.span_mono fun f hf => ?_
  exact (mem_intSub_PhiOne_iff f).mpr hf

theorem mem_subringSub_union_iff (hH : KerHyp M H p) [Nonempty (ModularForm.AtkinLehnerDatum M p)]
    (A : Subring ℂ) (f : CuspForm (Γ M H) 2) :
    f ∈ subringSub (PhiOne M H ∪ PhiTwo M H p hH) A ↔ f ∈ CuspForm.twoCuspIntegralSet M H 2 p A := by
  constructor
  · intro hf t ht W n
    exact ⟨hf _ (Or.inl ⟨t, ht, n, rfl⟩), hf _ (Or.inr ⟨t, ht, W, n, rfl⟩)⟩
  · intro hf φ hφ
    obtain ⟨W₀⟩ := ‹Nonempty (ModularForm.AtkinLehnerDatum M p)›
    rcases hφ with ⟨t, ht, n, rfl⟩ | ⟨t, ht, W, n, rfl⟩
    · exact (hf t ht W₀ n).1
    · exact (hf t ht W n).2

theorem twoCuspLattice_eq_subringSub (hH : KerHyp M H p) [Nonempty (ModularForm.AtkinLehnerDatum M p)]
    (A : Subring ℂ) :
    CuspForm.twoCuspLattice M H 2 p A = subringSub (PhiOne M H ∪ PhiTwo M H p hH) A := by
  have hset : CuspForm.twoCuspIntegralSet M H 2 p A =
      (subringSub (PhiOne M H ∪ PhiTwo M H p hH) A : Set (CuspForm (Γ M H) 2)) :=
    Set.ext fun f => (mem_subringSub_union_iff hH A f).symm
  rw [CuspForm.twoCuspLattice, hset, Submodule.span_eq]

theorem span_intSub_union_eq_top [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) (hH : KerHyp M H p) :
    Submodule.span ℂ (intSub (PhiOne M H ∪ PhiTwo M H p hH) : Set (CuspForm (Γ M H) 2)) = ⊤ := by
  classical

  obtain ⟨h, hli, hsp, hmem⟩ := exists_basis_intSub (separates_PhiOne (M := M) (H := H))
    span_intSub_PhiOne_eq_top
  have hhint : ∀ i, h i ∈ intSub (PhiOne M H) := fun i =>
    (hmem (h i)).mpr ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hspanℤ : ∀ w, w ∈ Submodule.span ℤ (Set.range h) → w ∈ intSub (PhiOne M H) := fun w hw =>
    (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hhint i)) hw

  have hcoefint : ∀ w ∈ intSub (PhiOne M H), ∀ n : ℕ, ∃ a : ℤ, coef n w = (a : ℂ) := fun w hw n => by
    obtain ⟨a, ha⟩ := hw _ (coef_comp_one_mem_PhiOne n)
    exact ⟨a, by simpa using ha⟩

  obtain ⟨D', hD', hclaim⟩ : ∃ D' : ℤ, D' ≠ 0 ∧
      ∀ f ∈ intSub (PhiOne M H), D' • f ∈ intSub (PhiOne M H ∪ PhiTwo M H p hH) := by
    rcases isEmpty_or_nonempty (ModularForm.AtkinLehnerDatum M p) with hE | ⟨⟨W₀⟩⟩
    · refine ⟨1, one_ne_zero, fun f hf φ hφ => ?_⟩
      rcases hφ with hφ | ⟨t, _, W, _⟩
      · rw [one_smul]; exact hf φ hφ
      · exact hE.elim W
    ·
      let vB : Module.Basis (Fin (Module.finrank ℂ (CuspForm (Γ M H) 2))) ℂ (CuspForm (Γ M H) 2) :=
        Module.Basis.mk hli hsp.ge
      have hvB : ∀ k, vB k = h k := fun k => by simp [vB]
      have hvB0 : ∀ k, vB k ∈ intSub (PhiZero M H) := by
        rintro k φ ⟨n, rfl⟩
        rw [hvB]
        exact hcoefint _ (hhint k) n
      obtain ⟨-, -, -, hrat⟩ := exists_smul_mem_span_int (separates_PhiZero (M := M) (H := H)) vB hvB0
      have hrange : Set.range vB = Set.range h := by
        ext x; constructor <;> rintro ⟨k, rfl⟩ <;> exact ⟨k, (hvB k).symm ▸ rfl⟩

      have hratj : ∀ j, ∀ φ ∈ PhiZero M H, ∃ r : ℚ, φ (alLin W₀ (hH W₀) 2 (h j)) = (r : ℂ) := by
        rintro j φ ⟨n, rfl⟩
        have hf : ∀ n : ℕ, ∃ r : ℚ, ModularFormClass.qCoeff (⇑(h j)) n = (r : ℂ) := fun n => by
          obtain ⟨a, ha⟩ := hcoefint _ (hhint j) n
          exact ⟨a, by rw [← coef_apply, ha]; push_cast; rfl⟩
        obtain ⟨r, hr⟩ := CuspForm.exists_ratCast_qCoeff_alSlash_of_forall_qCoeff_ratCast_gammaH p M hpM H
          hHp W₀ (h j) hf n
        exact ⟨r, by rw [coef_apply, coe_alLin, hr]⟩
      have hN : ∀ j, ∃ N : ℤ, N ≠ 0 ∧ ∀ n : ℕ, ∃ z : ℤ, (N : ℂ) * coef n (alLin W₀ (hH W₀) 2 (h j)) = z := by
        intro j
        obtain ⟨N, hN0, hNmem⟩ := hrat _ (hratj j)
        rw [hrange] at hNmem
        refine ⟨N, hN0, fun n => ?_⟩
        obtain ⟨z, hz⟩ := hcoefint _ (hspanℤ _ hNmem) n
        exact ⟨z, by rw [← hz, map_zsmul, zsmul_eq_mul]⟩
      choose N hN0 hNz using hN
      refine ⟨∏ j, N j, Finset.prod_ne_zero_iff.mpr fun j _ => hN0 j, fun f hf φ hφ => ?_⟩
      rcases hφ with hφ | ⟨t, ht, W, n, rfl⟩
      · obtain ⟨m, hm⟩ := hf φ hφ
        exact ⟨(∏ j, N j) * m, by rw [map_zsmul, hm, zsmul_eq_mul]; push_cast; ring⟩
      ·
        obtain ⟨m, hm⟩ := (hmem (t f)).mp (heckeRingH_mem_intSub_PhiOne ht hf)

        have hcj : ∀ j, ∃ z : ℤ, ((∏ i, N i : ℤ) : ℂ) * coef n (alLin W₀ (hH W₀) 2 (h j)) = z := by
          intro j
          obtain ⟨z, hz⟩ := hNz j n
          refine ⟨(∏ i ∈ Finset.univ.erase j, N i) * z, ?_⟩
          rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j)]
          push_cast
          rw [← hz]
          ring
        choose z hz using hcj
        refine ⟨∑ j, m j * z j, ?_⟩
        rw [map_zsmul, LinearMap.comp_apply, LinearMap.comp_apply, coef_apply, coe_alLin,
          alSlash_eq_alSlash W₀ W 2, ← coe_alLin W₀ (hH W₀), ← coef_apply, hm, map_sum, map_sum,
          zsmul_eq_mul, Finset.mul_sum]
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        have hzj := hz j
        push_cast at hzj
        rw [map_zsmul, map_zsmul, zsmul_eq_mul, ← hzj]
        ring

  rw [eq_top_iff, ← hsp, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hDi : (D' : ℤ) • h i ∈ intSub (PhiOne M H ∪ PhiTwo M H p hH) := hclaim _ (hhint i)
  have : h i = (D' : ℂ)⁻¹ • ((D' : ℤ) • h i) := by
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hD'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hDi)

theorem main [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    ∃ (n : ℕ) (b : Fin n → CuspForm (Γ M H) 2),
      LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧
        ∀ A : Subring ℂ, CuspForm.twoCuspLattice M H 2 p A = Submodule.span A (Set.range b) := by
  have hprime : p.Prime := Fact.out
  haveI : Nonempty (ModularForm.AtkinLehnerDatum M p) :=
    ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd hprime hpM hpM2
  have hH : KerHyp M H p := fun W =>
    hHp_transfer (Nat.div_dvd_of_dvd hpM) (R_dvd W) (Nat.div_eq_of_eq_mul_right W.q_pos W.hM) hHp
  obtain ⟨n, b, hli, hsp, hall⟩ := exists_basis_forall_subringSub_eq (separates_union hH)
    (span_intSub_union_eq_top hpM hHp hH)
  exact ⟨n, b, hli, hsp, fun A => by rw [twoCuspLattice_eq_subringSub hH A]; exact hall A⟩

end Assembly

end TwoCuspLatticeConc
p2m_reactivate "P2MW.S_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span.TwoCuspLatticeConc"

end
p2m_reactivate "P2MW.S_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span.TwoCuspLatticeConc"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    ∃ (n : ℕ) (b : Fin n → CuspForm (CohCarrier.GammaH M H) 2),
      LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧
        ∀ A : Subring ℂ, CuspForm.twoCuspLattice M H 2 p A = Submodule.span A (Set.range b) :=
  TwoCuspLatticeConc.main hpM hpM2 hHp

end S_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span
end P2MW
export P2MW.S_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span (solution)
