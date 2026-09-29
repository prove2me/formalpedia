-- Prove2me | solution 1 for CuspForm.span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ea5ffc7e-e452-5108-93fb-fa2ec094c973

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_diamondRaw_comm
import Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false

noncomputable section

namespace ShimuraDuality

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem span_setOf_forall_apply_intCast_eq_top
    (R : Subring (Module.End ℂ V)) (hcomm : ∀ s ∈ R, ∀ s' ∈ R, s * s' = s' * s)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι ℤ R)
    (hind : LinearIndependent ℂ fun i => ((e i : R) : Module.End ℂ V))
    (a₁ : Module.Dual ℂ V) (a : ℕ → Module.Dual ℂ V) (t : ℕ → R)
    (ha : ∀ (n : ℕ) (f : V), a n f = a₁ (((t n : R) : Module.End ℂ V) f))
    (hsep : ∀ f : V, (∀ n, a n f = 0) → f = 0) :
    Submodule.span ℂ {f : V | ∀ s ∈ R, ∀ n : ℕ, ∃ m : ℤ, a n (s f) = (m : ℂ)} = ⊤ := by
  classical
  let eC : ι → Module.End ℂ V := fun i => ((e i : R) : Module.End ℂ V)

  have hRcomb : ∀ s : R, (s : Module.End ℂ V) = ∑ i, (e.repr s i : ℂ) • eC i := by
    intro s
    have h := congrArg (fun x : R => (x : Module.End ℂ V)) (e.sum_repr s)
    simp only [AddSubmonoidClass.coe_finsetSum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    rfl

  let Ψ : V →ₗ[ℂ] (ι → ℂ) := LinearMap.pi fun i => a₁.comp (eC i)
  have hΨ : ∀ f i, Ψ f i = a₁ (eC i f) := fun f i => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have h0 : ∀ i, a₁ (eC i f) = 0 := fun i => by rw [← hΨ, hf]; rfl
    have hR : ∀ s : R, a₁ ((s : Module.End ℂ V) f) = 0 := fun s => by
      rw [hRcomb s, LinearMap.sum_apply, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.smul_apply, map_smul, h0 i, smul_zero]
    exact hsep f fun n => by rw [ha]; exact hR (t n)

  have hcommC : ∀ s ∈ Submodule.span ℂ (Set.range eC), ∀ n : ℕ,
      s * ((t n : R) : Module.End ℂ V) = ((t n : R) : Module.End ℂ V) * s := by
    intro s hs n
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨i, rfl⟩; exact hcomm _ (e i).2 _ (t n).2
    · simp
    · intro x y _ _ hx hy; rw [add_mul, mul_add, hx, hy]
    · intro c x _ hx; rw [smul_mul_assoc, mul_smul_comm, hx]
  let Θ : (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ V :=
    { toFun := fun c => a₁.comp (∑ i, c i • eC i)
      map_add' := fun c d => by
        ext f; simp [Finset.sum_add_distrib, add_smul]
      map_smul' := fun r c => by
        ext f
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          map_sum, map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  have hΘ : ∀ c f, Θ c f = a₁ ((∑ i, c i • eC i) f) := fun c f => rfl
  have hΘinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set s : Module.End ℂ V := ∑ i, c i • eC i with hs
    have hsmem : s ∈ Submodule.span ℂ (Set.range eC) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
    have h1 : ∀ f, a₁ (s f) = 0 := fun f => by rw [← hΘ, hc]; rfl
    have h2 : ∀ f, s f = 0 := fun f => hsep _ fun n => by
      rw [ha, ← Module.End.mul_apply, ← hcommC s hsmem n, Module.End.mul_apply, h1]
    have hs0 : s = 0 := LinearMap.ext h2

    have := hind
    rw [Fintype.linearIndependent_iff] at this
    exact funext (this c (by rw [← hs0]))
  have hcard : Fintype.card ι = finrank ℂ V := by
    apply le_antisymm
    · have := LinearMap.finrank_le_finrank_of_injective hΘinj
      rwa [finrank_fintype_fun_eq_card, Subspace.dual_finrank_eq] at this
    · have := LinearMap.finrank_le_finrank_of_injective hΨinj
      rwa [finrank_fintype_fun_eq_card] at this

  have hΨbij : Function.Bijective Ψ :=
    ⟨hΨinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_fintype_fun_eq_card, hcard])).mp hΨinj⟩
  let ΨE : V ≃ₗ[ℂ] (ι → ℂ) := LinearEquiv.ofBijective Ψ hΨbij

  let fam : ι → V := fun i => ΨE.symm (Pi.single i 1)
  have hfam : ∀ i j, a₁ (eC j (fam i)) = if j = i then 1 else 0 := by
    intro i j
    have : Ψ (fam i) = Pi.single i 1 := ΨE.apply_symm_apply (Pi.single i 1)
    rw [← hΨ, this, Pi.single_apply]
  have hint : ∀ i, ∀ s ∈ R, ∀ n : ℕ, ∃ m : ℤ, a n (s (fam i)) = (m : ℂ) := by
    intro i s hs n
    refine ⟨e.repr (t n * ⟨s, hs⟩) i, ?_⟩
    rw [ha, ← Module.End.mul_apply]
    have hmul : ((t n : R) : Module.End ℂ V) * s = ((t n * ⟨s, hs⟩ : R) : Module.End ℂ V) := rfl
    rw [hmul, hRcomb (t n * ⟨s, hs⟩), LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smul_apply, map_smul, hfam i, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

  rw [eq_top_iff]
  have hspan : Submodule.span ℂ (Set.range fam) = ⊤ := by
    have hb : Submodule.span ℂ (Set.range fun i : ι => (Pi.single i (1 : ℂ) : ι → ℂ)) = ⊤ := by
      rw [← (Pi.basisFun ℂ ι).span_eq]
      congr 1
      ext x
      simp [Pi.basisFun_apply]
    have : Set.range fam = (ΨE.symm : (ι → ℂ) →ₗ[ℂ] V) '' Set.range (fun i : ι => (Pi.single i (1 : ℂ) : ι → ℂ)) := by
      ext x; simp [fam, Set.mem_image, Set.mem_range]
    rw [this, Submodule.span_image, hb, Submodule.map_top, LinearEquiv.range]
  rw [← hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subset_span (hint i)

end ShimuraDuality

open scoped MatrixGroups TensorProduct ModularForm Pointwise
open CongruenceSubgroup

namespace ShimuraIntegral

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H

abbrev Γr : Subgroup (GL (Fin 2) ℝ) := ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev V : Type := CuspForm (CohCarrier.GammaH M H) 2

abbrev PL : Submodule ℤ (Module.Dual ℂ (V M H)) := ModularCurve.periodLatticeOf (Gam M H)

abbrev TT : Subring (V M H →ₗ[ℂ] V M H) := CuspForm.heckeRingH M H 2

section Shortcuts

scoped instance (priority := high) instAddCommGroupV : AddCommGroup (V M H) := inferInstance
scoped instance (priority := high) instModuleV : Module ℂ (V M H) := inferInstance
scoped instance (priority := high) instAddCommGroupDualV : AddCommGroup (Module.Dual ℂ (V M H)) := inferInstance
scoped instance (priority := high) instModuleDualV : Module ℂ (Module.Dual ℂ (V M H)) := inferInstance
scoped instance (priority := high) instAddCommGroupPL : AddCommGroup (PL M H) := inferInstance
scoped instance (priority := high) instAddCommMonoidPL : AddCommMonoid (PL M H) := inferInstance
scoped instance (priority := high) instModulePL : Module ℤ (PL M H) := inferInstance
scoped instance (priority := high) instRingTT : Ring (TT M H) := inferInstance
scoped instance (priority := high) instSemiringTT : Semiring (TT M H) := inferInstance
scoped instance (priority := high) instNonAssocRingTT : NonAssocRing (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalNonAssocRingTT : NonUnitalNonAssocRing (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalRingTT : NonUnitalRing (TT M H) := inferInstance
scoped instance (priority := high) instNonAssocSemiringTT : NonAssocSemiring (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalNonAssocSemiringTT :
    NonUnitalNonAssocSemiring (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalSemiringTT : NonUnitalSemiring (TT M H) := inferInstance
scoped instance (priority := high) instAddCommGroupTT : AddCommGroup (TT M H) := inferInstance
scoped instance (priority := high) instAddCommMonoidTT : AddCommMonoid (TT M H) := inferInstance
scoped instance (priority := high) instAddGroupTT : AddGroup (TT M H) := inferInstance
scoped instance (priority := high) instAddMonoidTT : AddMonoid (TT M H) := inferInstance
scoped instance (priority := high) instMonoidTT : Monoid (TT M H) := inferInstance
scoped instance (priority := high) instMulOneClassTT : MulOneClass (TT M H) := inferInstance
scoped instance (priority := high) instMulZeroClassTT : MulZeroClass (TT M H) := inferInstance
scoped instance (priority := high) instAddMonoidWithOneTT : AddMonoidWithOne (TT M H) := inferInstance
scoped instance (priority := high) instAddGroupWithOneTT : AddGroupWithOne (TT M H) := inferInstance
scoped instance (priority := high) instMulTT : Mul (TT M H) := inferInstance
scoped instance (priority := high) instAddTT : Add (TT M H) := inferInstance
scoped instance (priority := high) instZeroTT : Zero (TT M H) := inferInstance
scoped instance (priority := high) instOneTT : One (TT M H) := inferInstance
scoped instance (priority := high) instNegTT : Neg (TT M H) := inferInstance
scoped instance (priority := high) instSubTT : Sub (TT M H) := inferInstance
scoped instance (priority := high) instModuleIntTT : Module ℤ (TT M H) := inferInstance

end Shortcuts

theorem isCong : IsCongruenceSubgroup (Gam M H) :=
  ⟨M, NeZero.ne M, CuspForm.Gamma_le_GammaH M H⟩

theorem periodOf_eq_pm (f : V M H) (δ : Gam M H) :
    ModularCurve.periodOf (Gam M H) δ f =
      ModularCurve.periodMapOf (Gam M H) f (Additive.ofMul δ) :=
  (ModularCurve.periodMapOf_apply_eq_periodOf (Gam M H) f δ).symm

theorem pm_injective : Function.Injective (ModularCurve.periodMapOf (Gam M H)) := by
  intro f g hfg
  have h0 : f - g = 0 := by
    apply ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Gam M H)
    intro γ
    rw [map_sub, periodOf_eq_pm, periodOf_eq_pm, hfg, sub_self, Complex.zero_re]
  exact sub_eq_zero.mp h0

theorem pm_heckeT {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : V M H) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMapOf (Gam M H) (CuspForm.heckeTLinH 2 hℓ hℓM f) =
      CohCarrier.heckeT M H ℓ ℂ (ModularCurve.periodMapOf (Gam M H) f) :=
  ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 hℓ hℓM)
    f _ (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

theorem pm_heckeU {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : V M H) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.periodMapOf (Gam M H) (CuspForm.heckeULinH 2 q f) =
      CohCarrier.heckeT M H q ℂ (ModularCurve.periodMapOf (Gam M H) f) :=
  ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU M H hq hqM f _
    (CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) f)

theorem pm_diamond (d : (ZMod M)ˣ) (σ : Gamma0 M) (hσ : CohCarrier.gamma0Units M σ = d)
    (f : V M H) :
    ModularCurve.periodMapOf (Gam M H) (CuspForm.diamondLinH 2 d f) =
      CohCarrier.diamondRaw M H ℂ σ (ModularCurve.periodMapOf (Gam M H) f) :=
  ModularCurve.periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash M H σ f _
    (CuspForm.coe_diamondLinH_eq_slash 2 (CuspForm.stableD M H 2) d σ hσ f)

theorem exists_lift (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, CohCarrier.gamma0Units M σ = d ∧
      ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 := by
  haveI : NeZero (ℓ * M) := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne M)⟩
  have hdvd : M ∣ ℓ * M := dvd_mul_left M ℓ
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdvd d
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective (ℓ * M) u
  have hτ10 : ((((τ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod (ℓ * M)) = 0 := Gamma0_mem.mp τ.2
  have hdiv : ((ℓ * M : ℕ) : ℤ) ∣ (τ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hτ10
  have hσ0 : (τ : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem]
    have hM : ((M : ℕ) : ℤ) ∣ (τ : SL(2, ℤ)) 1 0 :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hdiv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hM
  refine ⟨⟨τ, hσ0⟩, ?_, hdiv⟩
  rw [← hu, ← hτ]
  ext
  rw [ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  simp [Gamma0Map]

theorem shadow_cases (g : CohCarrier.Gen M (∅ : Set ℕ)) :
    (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ∀ f : V M H,
        ModularCurve.periodMapOf (Gam M H) (CuspForm.heckeGenH (H := H) ∅ 2 g f) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            CohCarrier.heckeT M H ℓ ℂ (ModularCurve.periodMapOf (Gam M H) f))) ∨
    (∃ d : (ZMod M)ˣ, CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2 g = CuspForm.diamondLinH 2 d) := by
  cases g with
  | T ℓ hℓ hS hℓM => exact Or.inl ⟨ℓ, hℓ, fun f => pm_heckeT M H hℓ hℓM f⟩
  | U q hq hqM => exact Or.inl ⟨q, hq, fun f => pm_heckeU M H hq hqM f⟩
  | dia d => exact Or.inr ⟨d, rfl⟩

theorem gen_comm (g₁ g₂ : CohCarrier.Gen M (∅ : Set ℕ)) :
    CuspForm.heckeGenH (H := H) ∅ 2 g₁ * CuspForm.heckeGenH ∅ 2 g₂ =
      CuspForm.heckeGenH ∅ 2 g₂ * CuspForm.heckeGenH ∅ 2 g₁ := by
  apply LinearMap.ext
  intro f
  apply pm_injective M H
  simp only [Module.End.mul_apply]
  rcases shadow_cases M H g₁ with ⟨ℓ₁, hℓ₁, h₁⟩ | ⟨d₁, h₁⟩ <;>
    rcases shadow_cases M H g₂ with ⟨ℓ₂, hℓ₂, h₂⟩ | ⟨d₂, h₂⟩
  · haveI : NeZero ℓ₁ := ⟨hℓ₁.ne_zero⟩
    haveI : NeZero ℓ₂ := ⟨hℓ₂.ne_zero⟩
    rw [h₁, h₂, h₂, h₁]
    by_cases heq : ℓ₁ = ℓ₂
    · subst heq
      rfl
    · exact CohCarrier.heckeT_comm_of_prime M H ℓ₁ ℓ₂ hℓ₁
        ((Nat.coprime_primes hℓ₁ hℓ₂).mpr heq) _
  · haveI : NeZero ℓ₁ := ⟨hℓ₁.ne_zero⟩
    obtain ⟨σ, hσ, hdiv⟩ := exists_lift M ℓ₁ d₂
    rw [h₁, h₂, pm_diamond M H d₂ σ hσ, pm_diamond M H d₂ σ hσ, h₁]
    exact CohCarrier.heckeT_diamondRaw_comm M H ℓ₁ σ hdiv _
  · haveI : NeZero ℓ₂ := ⟨hℓ₂.ne_zero⟩
    obtain ⟨σ, hσ, hdiv⟩ := exists_lift M ℓ₂ d₁
    rw [h₁, h₂, pm_diamond M H d₁ σ hσ, pm_diamond M H d₁ σ hσ, h₂]
    exact (CohCarrier.heckeT_diamondRaw_comm M H ℓ₂ σ hdiv _).symm
  · rw [h₁, h₂, pm_diamond M H d₁ (CuspForm.gammaLift M d₁) (CuspForm.gamma0Units_gammaLift d₁),
      pm_diamond M H d₂ (CuspForm.gammaLift M d₂) (CuspForm.gamma0Units_gammaLift d₂),
      pm_diamond M H d₂ (CuspForm.gammaLift M d₂) (CuspForm.gamma0Units_gammaLift d₂),
      pm_diamond M H d₁ (CuspForm.gammaLift M d₁) (CuspForm.gamma0Units_gammaLift d₁)]
    exact CohCarrier.diamondRaw_comm M H _ _ _

theorem heckeRingH_le_centralizer :
    TT M H ≤ Subring.centralizer (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2)) := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨g₁, rfl⟩
  rw [SetLike.mem_coe, Subring.mem_centralizer_iff]
  rintro _ ⟨g₂, rfl⟩
  exact gen_comm M H g₂ g₁

theorem hecke_comm (s t : TT M H) : s * t = t * s := by
  have h1 : (t : V M H →ₗ[ℂ] V M H) ∈
      Subring.centralizer (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2)) :=
    heckeRingH_le_centralizer M H t.2
  have h2 : TT M H ≤ Subring.centralizer {(t : V M H →ₗ[ℂ] V M H)} := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ((Subring.mem_centralizer_iff.mp h1) _ ⟨g, rfl⟩).symm
  have h3 := Subring.mem_centralizer_iff.mp (h2 s.2) _ (Set.mem_singleton _)
  exact Subtype.ext h3.symm

omit [NeZero M] in

theorem exists_heckeT_universal (ℓ : ℕ) [NeZero ℓ] (δ : Gam M H) :
    ∃ γ₀ : Gam M H, ∀ (A : Type) [AddCommGroup A] (φ : CohCarrier.H1 M H A),
      CohCarrier.heckeT M H ℓ A φ (Additive.ofMul δ) = φ (Additive.ofMul γ₀) := by
  let U : Type := Additive (Abelianization (Gam M H))
  let u : CohCarrier.H1 M H U := MonoidHom.toAdditive (Abelianization.of (G := Gam M H))
  obtain ⟨γ₀, hγ₀⟩ := (QuotientGroup.mk_surjective (s := commutator (Gam M H)))
    (Additive.toMul (CohCarrier.heckeT M H ℓ U u (Additive.ofMul δ)))
  refine ⟨γ₀, fun A _ φ => ?_⟩
  let φ' : U →+ A :=
    MonoidHom.toAdditiveLeft (Abelianization.lift (AddMonoidHom.toMultiplicativeRight φ))
  have hφ : φ = φ'.comp u := by
    ext a
    simp [φ', u, MonoidHom.toAdditiveLeft, AddMonoidHom.toMultiplicativeRight, MonoidHom.toAdditive]
  rw [hφ, CohCarrier.heckeT_comp_coeff M H ℓ φ' u, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply]
  congr 1
  change _ = Additive.ofMul (Abelianization.of γ₀)
  change _ = Additive.ofMul (QuotientGroup.mk γ₀)
  rw [hγ₀, ofMul_toMul]

theorem exists_gen_universal (g : CohCarrier.Gen M (∅ : Set ℕ)) (δ : Gam M H) :
    ∃ γ₀ : Gam M H,
      ∀ f : V M H, ModularCurve.periodOf (Gam M H) δ (CuspForm.heckeGenH (H := H) ∅ 2 g f) =
        ModularCurve.periodOf (Gam M H) γ₀ f := by
  cases g with
  | T ℓ hℓ hS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨γ₀, h⟩ := exists_heckeT_universal M H ℓ δ
    refine ⟨γ₀, fun f => ?_⟩
    rw [periodOf_eq_pm, periodOf_eq_pm, CuspForm.heckeGenH_T, pm_heckeT M H hℓ hℓM f]
    exact h ℂ _
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨γ₀, h⟩ := exists_heckeT_universal M H q δ
    refine ⟨γ₀, fun f => ?_⟩
    rw [periodOf_eq_pm, periodOf_eq_pm, CuspForm.heckeGenH_U, pm_heckeU M H hq hqM f]
    exact h ℂ _
  | dia d =>
    refine ⟨CohCarrier.conjHom M H (CuspForm.gammaLift M d) δ, fun f => ?_⟩
    rw [periodOf_eq_pm, periodOf_eq_pm, CuspForm.heckeGenH_dia,
      pm_diamond M H d (CuspForm.gammaLift M d) (CuspForm.gamma0Units_gammaLift d) f]
    rfl

theorem dualMap_gen_periodOf (g : CohCarrier.Gen M (∅ : Set ℕ)) (δ γ₀ : Gam M H)
    (h : ∀ f : V M H, ModularCurve.periodOf (Gam M H) δ (CuspForm.heckeGenH (H := H) ∅ 2 g f) =
        ModularCurve.periodOf (Gam M H) γ₀ f) :
    (CuspForm.heckeGenH (H := H) ∅ 2 g).dualMap (ModularCurve.periodOf (Gam M H) δ) =
      ModularCurve.periodOf (Gam M H) γ₀ :=
  LinearMap.ext fun f => by rw [LinearMap.dualMap_apply, h]

theorem dualMap_mem_of_mem {t : V M H →ₗ[ℂ] V M H} (ht : t ∈ TT M H)
    {v : Module.Dual ℂ (V M H)} (hv : v ∈ PL M H) : t.dualMap v ∈ PL M H := by
  have ht' : t ∈ Subring.closure (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2)) := ht
  clear ht
  induction ht' using Subring.closure_induction generalizing v with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨δ, rfl⟩ := hw
      obtain ⟨γ₀, hper⟩ := exists_gen_universal M H g δ
      rw [dualMap_gen_periodOf M H g δ γ₀ hper]
      exact ModularCurve.periodOf_mem_periodLatticeOf _ _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul n w _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ n ih
  | zero =>
    have : (0 : V M H →ₗ[ℂ] V M H).dualMap v = 0 := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact Submodule.zero_mem _
  | one =>
    have : (1 : V M H →ₗ[ℂ] V M H).dualMap v = v := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact hv
  | add x y _ _ hx hy =>
    have : (x + y).dualMap v = x.dualMap v + y.dualMap v := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact Submodule.add_mem _ (hx hv) (hy hv)
  | neg x _ hx =>
    have : (-x).dualMap v = -(x.dualMap v) := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact Submodule.neg_mem _ (hx hv)
  | mul x y _ _ hx hy =>
    have : (x * y).dualMap v = y.dualMap (x.dualMap v) := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact hy (hx hv)

def Pend (t : TT M H) : PL M H →ₗ[ℤ] PL M H where
  toFun v := ⟨(t : V M H →ₗ[ℂ] V M H).dualMap v, dualMap_mem_of_mem M H t.2 v.2⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' n v := Subtype.ext (by simp [map_zsmul])

theorem Pend_apply_apply (t : TT M H) (v : PL M H) (f : V M H) :
    ((Pend M H t v : PL M H) : Module.Dual ℂ (V M H)) f =
      (v : Module.Dual ℂ (V M H)) ((t : V M H →ₗ[ℂ] V M H) f) :=
  rfl

theorem Pend_add (s t : TT M H) : Pend M H (s + t) = Pend M H s + Pend M H t :=
  LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun f => by
    simp only [LinearMap.add_apply, Submodule.coe_add, Pend_apply_apply, Subring.coe_add, map_add])

theorem Pend_zero : Pend M H 0 = 0 :=
  LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun f => by
    simp only [LinearMap.zero_apply, Submodule.coe_zero, Pend_apply_apply, Subring.coe_zero, map_zero])

def PendL : TT M H →ₗ[ℤ] (PL M H →ₗ[ℤ] PL M H) :=
  AddMonoidHom.toIntLinearMap
    { toFun := Pend M H
      map_zero' := Pend_zero M H
      map_add' := Pend_add M H }

@[scoped simp] theorem PendL_apply (t : TT M H) : PendL M H t = Pend M H t := rfl

theorem Pend_eq_zero (t : TT M H) (ht : Pend M H t = 0) : t = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  have hper : ∀ δ : Gam M H,
      ModularCurve.periodOf (Gam M H) δ ((t : V M H →ₗ[ℂ] V M H) f) = 0 := fun δ => by
    have := congrArg (fun P : PL M H →ₗ[ℤ] PL M H =>
      ((P ⟨ModularCurve.periodOf (Gam M H) δ, ModularCurve.periodOf_mem_periodLatticeOf _ δ⟩ :
        PL M H) : Module.Dual ℂ (V M H)) f) ht
    simpa [Pend_apply_apply] using this
  have h0 := ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Gam M H)
    ((t : V M H →ₗ[ℂ] V M H) f) (fun δ => by rw [hper δ, Complex.zero_re])
  simpa using h0

theorem PendL_injective : Function.Injective (PendL M H) := by
  intro s t hst
  have h : PendL M H (s - t) = 0 := by rw [map_sub, hst, sub_self]
  exact sub_eq_zero.mp (Pend_eq_zero M H _ h)

scoped instance instModuleFiniteTT : Module.Finite ℤ (TT M H) := by
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (Gam M H) (isCong M H)
  haveI : Module.Free ℤ (PL M H) := Module.Free.of_basis b
  haveI : Module.Finite ℤ (PL M H) := Module.Finite.of_basis b
  exact Module.Finite.of_injective (PendL M H) (PendL_injective M H)

scoped instance instModuleFreeTT : Module.Free ℤ (TT M H) := by
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (Gam M H) (isCong M H)
  haveI : Module.Free ℤ (PL M H) := Module.Free.of_basis b
  haveI : Module.Finite ℤ (PL M H) := Module.Finite.of_basis b
  haveI : Module.Free ℤ (PL M H →ₗ[ℤ] PL M H) := Module.Free.linearMap _ _ _ _
  haveI : Module.Flat ℤ (PL M H →ₗ[ℤ] PL M H) := Module.Flat.of_free
  haveI : Module.IsTorsionFree ℤ (PL M H →ₗ[ℤ] PL M H) := Module.Flat.isTorsionFree
  haveI : Module.IsTorsionFree ℤ (TT M H) :=
    (PendL_injective M H).moduleIsTorsionFree (PendL M H) (fun r x => map_zsmul _ r x)
  exact Module.free_of_finite_type_torsion_free'

scoped instance (priority := high) instAddCommGroupTensorPL : AddCommGroup (ℝ ⊗[ℤ] PL M H) := inferInstance
scoped instance (priority := high) instAddCommMonoidTensorPL : AddCommMonoid (ℝ ⊗[ℤ] PL M H) := inferInstance
scoped instance (priority := high) instModuleTensorPL : Module ℝ (ℝ ⊗[ℤ] PL M H) := inferInstance
scoped instance (priority := high) instModuleIntTensorPL : Module ℤ (ℝ ⊗[ℤ] PL M H) := inferInstance
scoped instance (priority := high) instRingEndTensorPL : Ring (Module.End ℝ (ℝ ⊗[ℤ] PL M H)) := inferInstance
scoped instance (priority := high) instAddCommGroupEndTensorPL :
    AddCommGroup (Module.End ℝ (ℝ ⊗[ℤ] PL M H)) := inferInstance
scoped instance (priority := high) instModuleEndTensorPL :
    Module ℝ (Module.End ℝ (ℝ ⊗[ℤ] PL M H)) := inferInstance

section BaseChange

variable {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module R N]

theorem liftBaseChange_baseChangeHom_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R N) :
    Function.Injective ((LinearMap.baseChangeHom R A N N).liftBaseChange A) := by
  classical
  set κ := (LinearMap.baseChangeHom R A N N).liftBaseChange A
  let BR := Algebra.TensorProduct.basis A b.end
  let B' := (Algebra.TensorProduct.basis A b).end
  have hκ : κ = (BR.equiv B' (Equiv.refl _)).toLinearMap := by
    refine BR.ext (fun ij => ?_)
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp only [κ, BR, B', Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul,
      LinearMap.baseChangeHom_apply, one_smul, Module.Basis.baseChange_end]
  rw [hκ]
  exact (BR.equiv B' _).injective

end BaseChange

theorem linearIndependent_baseChange_Pend {ι : Type*} (τ : Module.Basis ι ℤ (TT M H)) :
    LinearIndependent ℝ (fun k => (Pend M H (τ k)).baseChange ℝ) := by
  classical
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (Gam M H) (isCong M H)
  have hker : LinearMap.ker (PendL M H) = ⊥ := LinearMap.ker_eq_bot.mpr (PendL_injective M H)
  have h1 : LinearIndependent ℤ (fun k => PendL M H (τ k)) := τ.linearIndependent.map' _ hker
  have h2 : LinearIndependent ℝ (fun k => (1 : ℝ) ⊗ₜ[ℤ] PendL M H (τ k)) :=
    Module.Flat.linearIndependent_one_tmul h1
  set κ := (LinearMap.baseChangeHom ℤ ℝ (PL M H) (PL M H)).liftBaseChange ℝ
  have hκ : LinearMap.ker κ = ⊥ :=
    LinearMap.ker_eq_bot.mpr (liftBaseChange_baseChangeHom_injective (A := ℝ) b)
  have h3 := h2.map' κ hκ
  convert h3 using 1 <;> try rfl
  funext k
  simp only [Function.comp_apply, κ, LinearMap.liftBaseChange_tmul, LinearMap.baseChangeHom_apply,
    one_smul, PendL_apply]

omit [NeZero M] in

theorem real_smul_dual (r : ℝ) (φ : Module.Dual ℂ (V M H)) : r • φ = (r : ℂ) • φ := by
  ext f
  simp [Complex.real_smul]

theorem eq_zero_of_sum_real_smul_eq_zero {ι : Type*} [Fintype ι] (τ : Module.Basis ι ℤ (TT M H))
    (x : ι → ℝ) (hx : ∑ k, ((x k : ℝ) : ℂ) • ((τ k : TT M H) : V M H →ₗ[ℂ] V M H) = 0) : x = 0 := by
  classical
  obtain ⟨n, b, hbind, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (Gam M H) (isCong M H)

  have key : ∀ j : Fin n,
      ∑ k, ((x k : ℝ) : ℂ) • ((Pend M H (τ k) (b j) : PL M H) : Module.Dual ℂ (V M H)) = 0 := by
    intro j
    apply LinearMap.ext
    intro f
    have h := congrArg (fun T : V M H →ₗ[ℂ] V M H => ((b j : PL M H) : Module.Dual ℂ (V M H)) (T f)) hx
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, map_zero, map_sum,
      map_smul] at h
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simpa only [LinearMap.smul_apply, Pend_apply_apply] using h

  let θ : ℝ ⊗[ℤ] PL M H →ₗ[ℝ] Module.Dual ℂ (V M H) := ((PL M H).subtype).liftBaseChange ℝ
  have hθ : ∀ (r : ℝ) (v : PL M H), θ (r ⊗ₜ v) = r • (v : Module.Dual ℂ (V M H)) := fun r v => by
    simp [θ, LinearMap.liftBaseChange_tmul]
  let bR := Algebra.TensorProduct.basis ℝ b
  have hbR : ∀ i, bR i = (1 : ℝ) ⊗ₜ (b i) := fun i => Algebra.TensorProduct.basis_apply b i
  have hθinj : ∀ z, θ z = 0 → z = 0 := by
    intro z hz
    have hz' : ∑ i, (bR.repr z i) • ((b i : PL M H) : Module.Dual ℂ (V M H)) = 0 := by
      have := congrArg θ (bR.sum_repr z)
      rw [map_sum, hz] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hbR, hθ, one_smul]
    have hc := Fintype.linearIndependent_iff.mp hbind (fun i => bR.repr z i) hz'
    rw [← bR.sum_repr z]
    exact Finset.sum_eq_zero fun i _ => by rw [show bR.repr z i = 0 from hc i, zero_smul]

  have keyR : ∀ j : Fin n, ∑ k, x k • ((1 : ℝ) ⊗ₜ[ℤ] (Pend M H (τ k) (b j))) = 0 := by
    intro j
    apply hθinj
    rw [map_sum]
    have : ∀ k, θ (x k • ((1 : ℝ) ⊗ₜ[ℤ] (Pend M H (τ k) (b j)))) =
        ((x k : ℝ) : ℂ) • ((Pend M H (τ k) (b j) : PL M H) : Module.Dual ℂ (V M H)) := fun k => by
      rw [map_smul, hθ, one_smul, real_smul_dual]
    simp only [this]
    exact key j

  have hend : ∑ k, x k • (Pend M H (τ k)).baseChange ℝ = 0 := by
    refine bR.ext fun j => ?_
    rw [LinearMap.zero_apply, LinearMap.sum_apply]
    have : ∀ k, (x k • (Pend M H (τ k)).baseChange ℝ) (bR j) =
        x k • ((1 : ℝ) ⊗ₜ[ℤ] (Pend M H (τ k) (b j))) := fun k => by
      rw [LinearMap.smul_apply, hbR, LinearMap.baseChange_tmul]
    simp only [this]
    exact keyR j
  have hind := linearIndependent_baseChange_Pend M H τ
  funext k
  exact Fintype.linearIndependent_iff.mp hind x hend k

section Involution

def conjJ (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet⟩

omit [NeZero M] in
@[scoped simp] theorem conjJ_apply_11 (γ : SL(2, ℤ)) : (conjJ γ) 1 1 = γ 1 1 := by simp [conjJ]

omit [NeZero M] in
@[scoped simp] theorem conjJ_apply_10 (γ : SL(2, ℤ)) : (conjJ γ) 1 0 = -γ 1 0 := by simp [conjJ]

theorem val_mapGL (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![((s 0 0 : ℤ) : ℝ), ((s 0 1 : ℤ) : ℝ); ((s 1 0 : ℤ) : ℝ), ((s 1 1 : ℤ) : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem val_J : ((UpperHalfPlane.J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 0; 0, 1] := rfl

theorem val_mapGL_T :
    ((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![1, 1; 0, 1] := by
  rw [mapGL_coe_eq, ModularGroup.coe_T]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem val_mapGL_T_inv :
    ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T⁻¹) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![1, -1; 0, 1] := by
  rw [mapGL_coe_eq, ModularGroup.coe_T_inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem mapGL_conjJ (γ : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (conjJ γ) : GL (Fin 2) ℝ) =
      UpperHalfPlane.J * Matrix.SpecialLinearGroup.mapGL ℝ γ * UpperHalfPlane.J := by
  apply Units.ext
  simp only [Units.val_mul, val_mapGL, val_J, Matrix.mul_fin_two]
  simp [conjJ]

theorem J_mul_J : UpperHalfPlane.J * UpperHalfPlane.J = 1 := by
  rw [← sq]; exact UpperHalfPlane.J_sq

theorem J_inv : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J :=
  inv_eq_of_mul_eq_one_right J_mul_J

theorem mapGL_heckeDiag_J (σ : SL(2, ℤ)) (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    Matrix.SpecialLinearGroup.mapGL ℝ σ * ModularForm.heckeDiagMatrix ℓ * UpperHalfPlane.J =
      UpperHalfPlane.J * Matrix.SpecialLinearGroup.mapGL ℝ (conjJ σ) * ModularForm.heckeDiagMatrix ℓ := by
  apply Units.ext
  simp only [Units.val_mul, val_mapGL, val_J, ModularForm.val_heckeDiagMatrix hℓ, Matrix.mul_fin_two]
  simp [conjJ]

theorem mapGL_J (σ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ σ * UpperHalfPlane.J =
      UpperHalfPlane.J * Matrix.SpecialLinearGroup.mapGL ℝ (conjJ σ) := by
  rw [mapGL_conjJ, ← mul_assoc, ← mul_assoc, J_mul_J, one_mul]

theorem J_heckeMatrix_J {q j : ℕ} (hq : q ≠ 0) (hjq : j ≤ q) :
    UpperHalfPlane.J * ModularForm.heckeMatrix q j * UpperHalfPlane.J =
      Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T⁻¹) * ModularForm.heckeMatrix q (q - j) := by
  apply Units.ext
  simp only [Units.val_mul, val_J, ModularForm.val_heckeMatrix hq, val_mapGL_T_inv, Matrix.mul_fin_two]
  rw [Nat.cast_sub hjq, Matrix.of.injective.eq_iff]
  simp only [neg_mul, one_mul, neg_neg, zero_mul, add_zero, mul_one, zero_add, mul_zero]
  ring_nf

theorem T_J : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T * UpperHalfPlane.J =
    UpperHalfPlane.J * Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T⁻¹) := by
  apply Units.ext
  simp only [Units.val_mul, val_J, val_mapGL_T, val_mapGL_T_inv, Matrix.mul_fin_two]
  simp

theorem J_T : UpperHalfPlane.J * Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T =
    Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T⁻¹) * UpperHalfPlane.J := by
  apply Units.ext
  simp only [Units.val_mul, val_J, val_mapGL_T, val_mapGL_T_inv, Matrix.mul_fin_two]
  simp

theorem T_heckeMatrix {q : ℕ} (hq : q ≠ 0) (b : ℕ) :
    Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T * ModularForm.heckeMatrix q b =
      ModularForm.heckeMatrix q (b + q) := by
  apply Units.ext
  simp only [Units.val_mul, ModularForm.val_heckeMatrix hq, val_mapGL_T, Matrix.mul_fin_two]
  simp

theorem heckeU_slash_J (k : ℤ) (q : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = F) :
    (ModularForm.heckeU k q F) ∣[k] UpperHalfPlane.J = ModularForm.heckeU k q (F ∣[k] UpperHalfPlane.J) := by
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · simp [ModularForm.heckeU_def]
  have hq : q ≠ 0 := hqpos.ne'

  have hF' : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T⁻¹) : GL (Fin 2) ℝ) = F := by
    conv_lhs => rw [← hF]
    rw [← SlashAction.slash_mul, ← map_mul, mul_inv_cancel, map_one, SlashAction.slash_one]
  have hFJ : (F ∣[k] UpperHalfPlane.J) ∣[k]
      (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T⁻¹) : GL (Fin 2) ℝ) = F ∣[k] UpperHalfPlane.J := by
    rw [← SlashAction.slash_mul, ← T_J, SlashAction.slash_mul, hF]
  have hFJ' : (F ∣[k] UpperHalfPlane.J) ∣[k]
      (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = F ∣[k] UpperHalfPlane.J := by
    rw [← SlashAction.slash_mul, J_T, SlashAction.slash_mul, hF']
  set G : ℕ → UpperHalfPlane → ℂ := fun i => (F ∣[k] UpperHalfPlane.J) ∣[k] ModularForm.heckeMatrix q i
    with hG
  have hterm : ∀ j, j ≤ q → (F ∣[k] ModularForm.heckeMatrix q j) ∣[k] UpperHalfPlane.J = G (q - j) := by
    intro j hj
    rw [← SlashAction.slash_mul,
      show ModularForm.heckeMatrix q j * UpperHalfPlane.J =
        UpperHalfPlane.J * (UpperHalfPlane.J * ModularForm.heckeMatrix q j * UpperHalfPlane.J) from by
          rw [← mul_assoc, ← mul_assoc, J_mul_J, one_mul],
      J_heckeMatrix_J hq hj, SlashAction.slash_mul, SlashAction.slash_mul, hFJ]
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  rw [ModularForm.heckeU_def, ModularForm.heckeU_def, SlashAction.sum_slash, Finset.sum_range_succ',
    Finset.sum_range_succ' G]
  congr 1
  · rw [← Finset.sum_range_reflect (fun i => G (i + 1)) n]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [hterm (j + 1) (by omega)]
    congr 1
    omega
  · rw [hterm 0 (Nat.zero_le _), Nat.sub_zero]
    simp only [hG]
    have e : ModularForm.heckeMatrix (n + 1) (n + 1) =
        Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T * ModularForm.heckeMatrix (n + 1) 0 := by
      rw [T_heckeMatrix hq 0, zero_add]
    rw [e, SlashAction.slash_mul, hFJ']

variable {M H}

omit [NeZero M] in
theorem T_mem_GammaH : ModularGroup.T ∈ Gam M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H

omit [NeZero M] in

theorem conjJ_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : conjJ γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at hγ ⊢
  rw [conjJ_apply_10, Int.cast_neg, hγ, neg_zero]

omit [NeZero M] in
theorem gamma0Units_conjJ (σ : Gamma0 M) :
    CohCarrier.gamma0Units M ⟨conjJ σ, conjJ_mem_Gamma0 σ.2⟩ = CohCarrier.gamma0Units M σ := by
  ext
  rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  show (((conjJ σ) 1 1 : ℤ) : ZMod M) = (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [conjJ_apply_11]

omit [NeZero M] in
theorem conjJ_mem_GammaH {γ : SL(2, ℤ)} (hγ : γ ∈ Gam M H) : conjJ γ ∈ Gam M H := by
  obtain ⟨hγ0, hγH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨conjJ_mem_Gamma0 hγ0, ?_⟩
  rw [gamma0Units_conjJ ⟨γ, hγ0⟩]
  exact hγH

omit [NeZero M] in

theorem le_conj_J : Γr M H ≤ ConjAct.toConjAct UpperHalfPlane.J⁻¹ • Γr M H := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨conjJ γ, conjJ_mem_GammaH hγ, ?_⟩
  show (Matrix.SpecialLinearGroup.mapGL ℝ (conjJ γ) : GL (Fin 2) ℝ)
    = UpperHalfPlane.J * Matrix.SpecialLinearGroup.mapGL ℝ γ * UpperHalfPlane.J⁻¹
  rw [J_inv, mapGL_conjJ]

def restrictCusp {k : ℤ} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) :
    CuspForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono h)

def slashCusp {k : ℤ} {Γ₁ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₁ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : CuspForm Γ₁ k) : CuspForm Γ₁ k :=
  restrictCusp hg (CuspForm.translate f g)

def rho (f : V M H) : V M H := slashCusp UpperHalfPlane.J le_conj_J f

omit [NeZero M] in
@[scoped simp] theorem coe_rho (f : V M H) : ⇑(rho f) = ⇑f ∣[(2 : ℤ)] UpperHalfPlane.J := rfl

omit [NeZero M] in
theorem rho_add (f g : V M H) : rho (f + g) = rho f + rho g := by
  apply DFunLike.coe_injective
  show ⇑(rho (f + g)) = ⇑(rho f + rho g)
  rw [CuspForm.coe_add, coe_rho, coe_rho, coe_rho, CuspForm.coe_add, SlashAction.add_slash]

omit [NeZero M] in
theorem rho_smul (c : ℂ) (f : V M H) : rho (c • f) = (starRingEnd ℂ) c • rho f := by
  apply DFunLike.coe_injective
  show ⇑(rho (c • f)) = ⇑((starRingEnd ℂ) c • rho f)
  rw [coe_rho, CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, coe_rho, ModularForm.smul_slash,
    UpperHalfPlane.sigma_J]
  rfl

omit [NeZero M] in
theorem rho_rho (f : V M H) : rho (rho f) = f := by
  apply DFunLike.coe_injective
  show ⇑(rho (rho f)) = ⇑f
  rw [coe_rho, coe_rho, ← SlashAction.slash_mul, J_mul_J, SlashAction.slash_one]

def rhoHom : V M H →+ V M H where
  toFun := rho
  map_zero' := by
    have h := rho_smul (M := M) (H := H) 0 0
    rwa [zero_smul, map_zero, zero_smul] at h
  map_add' := rho_add

omit [NeZero M] in
@[scoped simp] theorem rhoHom_apply (f : V M H) : rhoHom f = rho f := rfl

theorem rho_diamond (d : (ZMod M)ˣ) (f : V M H) :
    rho (CuspForm.diamondLinH 2 d f) = CuspForm.diamondLinH 2 d (rho f) := by
  set σ : Gamma0 M := CuspForm.gammaLift M d
  let σ' : Gamma0 M := ⟨conjJ σ, conjJ_mem_Gamma0 σ.2⟩
  have hσ' : CohCarrier.gamma0Units M σ' = d := by
    rw [gamma0Units_conjJ σ]; exact CuspForm.gamma0Units_gammaLift d
  apply DFunLike.coe_injective
  show ⇑(rho (CuspForm.diamondLinH 2 d f)) = ⇑(CuspForm.diamondLinH 2 d (rho f))
  rw [coe_rho, CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2) d f,
    CuspForm.coe_diamondLinH_eq_slash 2 (CuspForm.stableD M H 2) d σ' hσ' (rho f), coe_rho,
    ← SlashAction.slash_mul, ← SlashAction.slash_mul, mapGL_J]

theorem rho_heckeU {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : V M H) :
    rho (CuspForm.heckeULinH 2 q f) = CuspForm.heckeULinH 2 q (rho f) := by
  apply DFunLike.coe_injective
  show ⇑(rho (CuspForm.heckeULinH 2 q f)) = ⇑(CuspForm.heckeULinH 2 q (rho f))
  rw [coe_rho, CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) f,
    CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) (rho f), coe_rho]
  exact heckeU_slash_J 2 q ⇑f (SlashInvariantFormClass.slash_action_eq f _
    ⟨ModularGroup.T, T_mem_GammaH, rfl⟩)

theorem rho_heckeT {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : V M H) :
    rho (CuspForm.heckeTLinH 2 hℓ hℓM f) = CuspForm.heckeTLinH 2 hℓ hℓM (rho f) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  set σ : Gamma0 M := CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)
  let σ' : Gamma0 M := ⟨conjJ σ, conjJ_mem_Gamma0 σ.2⟩
  have hσ' : (((σ' : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := by
    show (((conjJ σ) 1 1 : ℤ) : ZMod M) = ℓ
    rw [conjJ_apply_11]
    exact CuspForm.gammaLift_apply_11 hℓ hℓM
  have hT : ⇑f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ ⟨ModularGroup.T, T_mem_GammaH, rfl⟩
  apply DFunLike.coe_injective
  show ⇑(rho (CuspForm.heckeTLinH 2 hℓ hℓM f)) = ⇑(CuspForm.heckeTLinH 2 hℓ hℓM (rho f))
  rw [coe_rho, CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f,
    CuspForm.coe_heckeTLinH_eq 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) σ' hσ' (rho f), coe_rho,
    SlashAction.add_slash, heckeU_slash_J 2 ℓ ⇑f hT, ← SlashAction.slash_mul,
    mapGL_heckeDiag_J σ ℓ hℓ.ne_zero, SlashAction.slash_mul, SlashAction.slash_mul, SlashAction.slash_mul]

theorem rho_gen (g : CohCarrier.Gen M (∅ : Set ℕ)) (f : V M H) :
    rho (CuspForm.heckeGenH (H := H) ∅ 2 g f) = CuspForm.heckeGenH (H := H) ∅ 2 g (rho f) := by
  cases g with
  | T ℓ hℓ hS hℓM => exact rho_heckeT hℓ hℓM f
  | U q hq hqM => exact rho_heckeU hq hqM f
  | dia d => exact rho_diamond d f

theorem rho_mem {t : V M H →ₗ[ℂ] V M H} (ht : t ∈ TT M H) (f : V M H) : rho (t f) = t (rho f) := by
  have ht' : t ∈ Subring.closure (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2)) := ht
  clear ht
  induction ht' using Subring.closure_induction generalizing f with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact rho_gen g f
  | zero =>
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
    exact (rhoHom (M := M) (H := H)).map_zero
  | one => rfl
  | add x y _ _ hx hy =>
    rw [LinearMap.add_apply, LinearMap.add_apply, rho_add, hx, hy]
  | neg x _ hx =>
    rw [LinearMap.neg_apply, LinearMap.neg_apply, ← hx]
    exact (rhoHom (M := M) (H := H)).map_neg (x f)
  | mul x y _ _ hx hy =>
    rw [Module.End.mul_apply, Module.End.mul_apply, hx, hy]

end Involution

theorem linearIndependent_complex {ι : Type*} [Fintype ι] (τ : Module.Basis ι ℤ (TT M H)) :
    LinearIndependent ℂ (fun k => ((τ k : TT M H) : V M H →ₗ[ℂ] V M H)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set x : ι → ℝ := fun k => (c k).re with hxdef
  set y : ι → ℝ := fun k => (c k).im with hydef
  set A : V M H →ₗ[ℂ] V M H := ∑ k, ((x k : ℝ) : ℂ) • ((τ k : TT M H) : V M H →ₗ[ℂ] V M H) with hA
  set B : V M H →ₗ[ℂ] V M H := ∑ k, ((y k : ℝ) : ℂ) • ((τ k : TT M H) : V M H →ₗ[ℂ] V M H) with hB

  have hAB : A + Complex.I • B = 0 := by
    rw [← hc, hA, hB, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← add_smul]
    congr 1
    rw [hxdef, hydef, mul_comm]
    exact Complex.re_add_im (c k)

  have hρA : ∀ f, rho (A f) = A (rho f) := fun f => by
    rw [hA, LinearMap.sum_apply, LinearMap.sum_apply, ← rhoHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, rhoHom_apply, rho_smul, Complex.conj_ofReal,
      rho_mem (τ k).2]
  have hρB : ∀ f, rho (B f) = B (rho f) := fun f => by
    rw [hB, LinearMap.sum_apply, LinearMap.sum_apply, ← rhoHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, rhoHom_apply, rho_smul, Complex.conj_ofReal,
      rho_mem (τ k).2]
  have hAB' : A - Complex.I • B = 0 := by
    apply LinearMap.ext
    intro g
    have h1 := congrArg (fun T : V M H →ₗ[ℂ] V M H => rho (T (rho g))) hAB
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h1
    rw [rho_add, rho_smul, hρA, hρB, rho_rho, Complex.conj_I, neg_smul, ← sub_eq_add_neg] at h1
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply, h1]
    exact (rhoHom (M := M) (H := H)).map_zero
  have hA0 : A = 0 := by
    have h2 : (2 : ℂ) • A = 0 := by
      rw [two_smul]
      have := congrArg₂ (· + ·) hAB hAB'
      simp only [add_zero] at this
      rw [← this]
      abel
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hB0 : B = 0 := by
    have h2 : Complex.I • B = 0 := by rw [hA0, zero_add] at hAB; exact hAB
    exact (smul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hx := eq_zero_of_sum_real_smul_eq_zero M H τ x hA0
  have hy := eq_zero_of_sum_real_smul_eq_zero M H τ y hB0
  intro k
  apply Complex.ext
  · simpa [hxdef] using congrFun hx k
  · simpa [hydef] using congrFun hy k

section Coefficients

variable {M H}

omit [NeZero M] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γr M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_GammaH]
  exact AddSubgroup.mem_zmultiples _

omit [NeZero M] in
theorem isCusp_infty : IsCusp OnePoint.infty (Γr M H) :=
  Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods

def coef (n : ℕ) : V M H →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := by
    show PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑(f + g)) =
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑f) +
        PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑g)
    rw [CuspForm.coe_add, UpperHalfPlane.qExpansion_add
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods)
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods), map_add]
  map_smul' c f := by
    show PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑(c • f)) =
      c • PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑f)
    rw [CuspForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods), map_smul]

omit [NeZero M] in
theorem coef_apply (n : ℕ) (f : V M H) : coef n f = ModularFormClass.qCoeff (⇑f) n := rfl

omit [NeZero M] in
theorem coef_zero_eq (f : V M H) : coef 0 f = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods

omit [NeZero M] in

theorem eq_zero_of_forall_coef_eq_zero (f : V M H) (h : ∀ n, coef n f = 0) : f = 0 := by
  have hq : UpperHalfPlane.qExpansion 1 (⇑f) = 0 := by
    ext n
    rw [map_zero]
    exact h n
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods
  haveI : Fact (IsCusp OnePoint.infty (Γr M H)) := ⟨isCusp_infty⟩
  have hzero := (UpperHalfPlane.qExpansion_eq_zero_iff one_pos hper (CuspFormClass.holo f)
    (ModularFormClass.bdd_at_infty f)).mp hq
  exact DFunLike.coe_injective (hzero.trans CuspForm.coe_zero.symm)

theorem coef_heckeU {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : V M H) (n : ℕ) :
    coef n (CuspForm.heckeULinH 2 q f) = coef (n * q) f := by
  rw [coef_apply, coef_apply, CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) f,
    ModularFormClass.qCoeff_heckeU f one_mem_strictPeriods hq.ne_zero n, ModularForm.coeffHeckeU_apply]

omit [NeZero M] in

theorem periodic_heckeU (f : V M H) (q : ℕ) :
    Function.Periodic (ModularForm.heckeU 2 q ⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
  ModularForm.periodic_heckeU_comp_ofComplex
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods) 2 q

omit [NeZero M] in
private theorem _root_.ShimuraIntegral.mdifferentiable_heckeU (f : V M H) (q : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU 2 q ⇑f) :=
  ModularForm.mdifferentiable_heckeU f.holo' 2 q

p2m_export "ShimuraIntegral" "mdifferentiable_heckeU"
theorem isBoundedAtImInfty_heckeU (f : V M H) (q : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeU 2 q ⇑f) := by
  have hz : OnePoint.IsZeroAt OnePoint.infty (ModularForm.heckeU 2 q ⇑f) 2 :=
    CuspFormClass.isZeroAt_heckeU f q isCusp_infty
  rw [OnePoint.isZeroAt_infty_iff] at hz
  exact hz.boundedAtFilter

theorem analyticAt_cuspFunction_heckeU (f : V M H) (q : ℕ) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (ModularForm.heckeU 2 q ⇑f)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos (periodic_heckeU f q) (mdifferentiable_heckeU f q)
    (isBoundedAtImInfty_heckeU f q)

theorem coef_heckeT {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : V M H) (n : ℕ) :
    coef n (CuspForm.heckeTLinH 2 hℓ hℓM f) = coef (n * ℓ) f +
      (ℓ : ℂ) * (if ℓ ∣ n then
        coef (n / ℓ) (CuspForm.diamondLinH 2 (CuspForm.unitOfPrimeNotDvd hℓ hℓM) f) else 0) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0
  have hpow : (ℓ : ℂ) ^ ((2 : ℤ) - 1) = ℓ := by norm_num
  set F := CuspForm.heckeTLinH 2 hℓ hℓM f with hF
  set D := CuspForm.diamondLinH 2 (CuspForm.unitOfPrimeNotDvd hℓ hℓM) f with hD
  set U : UpperHalfPlane → ℂ := ModularForm.heckeU 2 ℓ ⇑f with hU

  have hcoeF : ⇑F = U + ⇑D ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ := by
    rw [hF, CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f, hD,
      CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2), SlashAction.slash_mul]

  set g : UpperHalfPlane → ℂ := fun τ => D (ModularForm.heckeDiagMatrix ℓ • τ) with hg
  have hgfun : g = ((ℓ : ℂ))⁻¹ • (⇑F - U) := by
    funext τ
    rw [Pi.smul_apply, Pi.sub_apply, hcoeF, Pi.add_apply, add_sub_cancel_left,
      ModularForm.slash_heckeDiagMatrix_apply 2 hℓ0, hpow, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hℓC,
      one_mul]

  have hanF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑F) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero F one_pos one_mem_strictPeriods
  have hanU : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 U) 0 := analyticAt_cuspFunction_heckeU f ℓ
  have hperFU : Function.Periodic ((⇑F - U) ∘ UpperHalfPlane.ofComplex) 1 := by
    have h1 := SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods
    have h2 := periodic_heckeU f ℓ
    intro z
    have e1 := h1 z
    have e2 := h2 z
    simp only [Function.comp_apply, Pi.sub_apply, Complex.ofReal_one] at e1 e2 ⊢
    rw [e1]
    exact congrArg (fun w => F (UpperHalfPlane.ofComplex z) - w) e2
  have hmdFU : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F - U) :=
    F.holo'.sub (mdifferentiable_heckeU f ℓ)
  have hbdFU : UpperHalfPlane.IsBoundedAtImInfty (⇑F - U) :=
    (ModularFormClass.bdd_at_infty F).sub (isBoundedAtImInfty_heckeU f ℓ)
  have hanFU : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑F - U)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperFU hmdFU hbdFU

  have hcg : ModularFormClass.qCoeff g n = ((ℓ : ℂ))⁻¹ * (coef n F - coef (n * ℓ) f) := by
    show PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 g) = _
    rw [hgfun, UpperHalfPlane.qExpansion_smul hanFU, UpperHalfPlane.qExpansion_sub hanF hanU, map_smul,
      map_sub, smul_eq_mul]
    congr 2
    change ModularFormClass.qCoeff U n = ModularFormClass.qCoeff (⇑f) (n * ℓ)
    rw [hU, ModularFormClass.qCoeff_heckeU f one_mem_strictPeriods hℓ0 n, ModularForm.coeffHeckeU_apply]
  have key := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul D one_mem_strictPeriods hℓ0 n
  change ModularFormClass.qCoeff g n = _ at key
  rw [hcg] at key
  have := congrArg (fun z => (ℓ : ℂ) * z) key
  simp only [← mul_assoc, mul_inv_cancel₀ hℓC, one_mul] at this
  rw [← coef_apply] at this
  linear_combination this

theorem exists_mem_coef_eq (n : ℕ) : ∃ t ∈ TT M H, ∀ f : V M H, coef n f = coef 1 (t f) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · refine ⟨0, Subring.zero_mem _, fun f => ?_⟩
      rw [coef_zero_eq, LinearMap.zero_apply, map_zero]
    · exact ⟨1, Subring.one_mem _, fun f => rfl⟩
  · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨m, rfl⟩ := hqn
    have hq1 : 1 < q := hq.one_lt
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hm : m < q * m := by nlinarith
    obtain ⟨tm, htm, hcm⟩ := ih m hm
    by_cases hqM : q ∣ M
    · refine ⟨tm * CuspForm.heckeULinH 2 q, Subring.mul_mem _ htm
        (CuspForm.heckeGenH_mem_heckeRingH (H := H) ∅ 2 (.U q hq hqM)), fun f => ?_⟩
      rw [Module.End.mul_apply, ← hcm, coef_heckeU hq hqM, mul_comm]
    · have hmq : m / q < q * m := lt_of_le_of_lt (Nat.div_le_self m q) hm
      obtain ⟨t', ht', hc'⟩ := ih (m / q) hmq
      set Tq := CuspForm.heckeTLinH (M := M) (H := H) 2 hq hqM with hTq
      set Dq := CuspForm.diamondLinH (M := M) (H := H) 2 (CuspForm.unitOfPrimeNotDvd hq hqM) with hDq
      have hTq_mem : Tq ∈ TT M H :=
        CuspForm.heckeGenH_mem_heckeRingH (H := H) ∅ 2 (.T q hq (Set.notMem_empty q) hqM)
      have hDq_mem : Dq ∈ TT M H := CuspForm.heckeGenH_mem_heckeRingH (H := H) ∅ 2 (.dia _)
      by_cases hqm : q ∣ m
      · refine ⟨tm * Tq - (q : V M H →ₗ[ℂ] V M H) * (t' * Dq),
          Subring.sub_mem _ (Subring.mul_mem _ htm hTq_mem)
            (Subring.mul_mem _ (natCast_mem (TT M H) q) (Subring.mul_mem _ ht' hDq_mem)), fun f => ?_⟩
        rw [LinearMap.sub_apply, map_sub, Module.End.mul_apply, ← hcm, coef_heckeT hq hqM, if_pos hqm,
          Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, ← hc',
          nsmul_eq_mul, mul_comm m q]
        ring
      · refine ⟨tm * Tq, Subring.mul_mem _ htm hTq_mem, fun f => ?_⟩
        rw [Module.End.mul_apply, ← hcm, coef_heckeT hq hqM, if_neg hqm, mul_zero, add_zero, mul_comm]

def tOf (n : ℕ) : TT M H :=
  ⟨Classical.choose (exists_mem_coef_eq (M := M) (H := H) n),
    (Classical.choose_spec (exists_mem_coef_eq (M := M) (H := H) n)).1⟩

theorem coef_eq_coef_one_tOf (n : ℕ) (f : V M H) :
    coef n f = coef 1 (((tOf n : TT M H) : V M H →ₗ[ℂ] V M H) f) :=
  (Classical.choose_spec (exists_mem_coef_eq (M := M) (H := H) n)).2 f

end Coefficients

theorem main :
    Submodule.span ℂ {f : V M H | ∀ t ∈ TT M H, ∀ n : ℕ,
        ∃ a : ℤ, ModularFormClass.qCoeff (⇑(t f)) n = (a : ℂ)} = ⊤ := by
  classical
  haveI : FiniteDimensional ℂ (V M H) := CuspForm.finiteDimensional_of_isArithmetic (Γr M H) 2
  let τ := Module.Free.chooseBasis ℤ (TT M H)
  exact ShimuraDuality.span_setOf_forall_apply_intCast_eq_top (V := V M H) (TT M H)
    (fun s hs s' hs' => congrArg Subtype.val (hecke_comm M H ⟨s, hs⟩ ⟨s', hs'⟩)) τ
    (linearIndependent_complex M H τ) (coef 1) (fun n => coef n) (fun n => tOf n)
    (fun n f => coef_eq_coef_one_tOf n f) (fun f hf => eq_zero_of_forall_coef_eq_zero f hf)

end ShimuraIntegral
p2m_reactivate "P2MW.S_CuspForm_span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top.ShimuraIntegral"

end
p2m_reactivate "P2MW.S_CuspForm_span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top.ShimuraIntegral"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    Submodule.span ℂ {f : CuspForm (CohCarrier.GammaH M H) 2 |
        ∀ t ∈ CuspForm.heckeRingH M H 2, ∀ n : ℕ,
          ∃ a : ℤ, ModularFormClass.qCoeff (⇑(t f)) n = (a : ℂ)} = ⊤ :=
  ShimuraIntegral.main M H

end S_CuspForm_span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top
end P2MW
export P2MW.S_CuspForm_span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top (solution)
