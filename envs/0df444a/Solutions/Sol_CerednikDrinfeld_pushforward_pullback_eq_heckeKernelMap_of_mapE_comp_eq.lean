-- Prove2me | solution 1 for CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2be43691-dc40-5301-889c-5f3e0c7fe396

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Theorems.Thm_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one
import Theorems.Thm_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd
import Theorems.Thm_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd
import Theorems.Thm_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_primeHeckeSet_mulVec_of_degTotal_eq
import Theorems.Thm_CerednikDrinfeld_classSetHeckeLaws_of_isEichlerOrder_meetOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.Gamma0Pair.isElliptic ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val ModularCurve.coe_levelAlphaC ModularCurve.SSLevelDatum.mk.sizeOf_spec ModularCurve.SSLevelDatum.mk.injEq ModularCurve.coe_levelBetaC ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld Finset

theorem solution

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      (if ℓ ∣ N then levelHeckeUSet Λ (meetOrder R n) ℓ else primeHeckeSet (meetOrder R n) ℓ))
    (hR' : IsEichlerOrder (meetOrder R s) (N * ℓ))
    (n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hS' : IsEichlerOrder (meetOrder (meetOrder R s) n') (N * ℓ * q))
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq' : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')),
      classSetShift _ n' (classSetShift _ n' x) = x)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]

    {E V E'' V'' : Type} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]
    [Fintype E''] [Fintype V''] [DecidableEq V''] [DecidableEq E'']
    (D : DegeneracyData E V) (D'' : DegeneracyData E'' V'')
    (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃ E)
    (hw : ∀ c, D.w (eE c) = (classSetDegeneracyData R n).w c)
    (eE'' : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) ≃ E'')
    (hw'' : ∀ c, D''.w (eE'' c) = (classSetDegeneracyData (meetOrder R s) n').w c)
    (e : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel (classSetDegeneracyData R n)))
    (he : ∀ (x : ↥(ribbonKernel D)) (c : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n))),
      ((e x : ↥(ribbonKernel (classSetDegeneracyData R n))) :
          ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) c = (x : E → ℤ) (eE c))

    (μ₀ μ₁ : D''.FiniteHom D)
    (h₀ : ∀ c, μ₀.mapE (eE'' c) = eE (classSetForget _ _ c))
    (h₁ : ∀ c, μ₁.mapE (eE'' c) = eE (ClassSet.mk _ (c.out * s)))
    (z : ↥(ribbonKernel (classSetDegeneracyData R n))) :
    e (μ₀.pushforward (μ₁.pullback (e.symm z))) =
      heckeKernelMap (classSetHeckeData N q Λ R n) ⟨ℓ, Fact.out⟩ z := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hlaws : ClassSetHeckeLaws N q Λ R n :=
    CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder N q q' hqq' hqN hq'N hdef Λ R hΛ hR hRΛ n hS hn

  have hy : ∀ c, ((e.symm z : ↥(ribbonKernel D)) : E → ℤ) (eE c) =
      (z : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) c := fun c => by
    rw [← he (e.symm z) c, LinearEquiv.apply_symm_apply]

  obtain ⟨α, β, -, hα, -, -, -, -, hβ, -, -, hdict⟩ :
      ∃ α β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n),
        α.mapV = classSetForget _ _ ∧ α.mapE = classSetForget _ _ ∧ True ∧ True ∧ True ∧
        (β.mapV = fun v => ClassSet.mk _ (v.out * s)) ∧ (β.mapE = fun e => ClassSet.mk _ (e.out * s)) ∧ True ∧ True ∧
        ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ,
          CerednikDrinfeld.pushforward α.mapE (β.pullbackFun x) =
            ((classSetHeckeData N q Λ R n).T ⟨ℓ, hℓp⟩).mulVec x := by
    by_cases hℓN : ℓ ∣ N
    · rw [if_pos hℓN] at hs
      obtain ⟨α, β, h1, h2, -, -, -, h6, h7, -, -, -⟩ :=
        CerednikDrinfeld.exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd
          hN hqN hq'N hqq' hq'5 hdef Λ R hΛ hR hRΛ n hn hS hnorm hsq ℓ hℓN s hs hR' n' hn' hS' hnorm' hsq' hnn' hsn'
      refine ⟨α, β, h1, h2, trivial, trivial, trivial, h6, h7, trivial, trivial, fun x => ?_⟩
      rw [CerednikDrinfeld.pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd
        hN hqN hq'N hqq' hq'5 hdef Λ R hΛ hR hRΛ n hn hS hnorm hsq ℓ hℓN s hs hR' n' hn' hS' hnorm' hsq' hnn' hsn' α β h2 h7 x]
      congr 1
      simp only [classSetHeckeData, dif_pos hlaws, classSetEdgeHecke, if_neg hℓq, if_pos hℓN]
    · rw [if_neg hℓN] at hs
      have hℓ3 : ¬ ℓ ∣ N * q * q' := by
        intro h
        rcases (Nat.Prime.dvd_mul hℓp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hℓp).mp h with h | h
          · exact hℓN h
          · exact hℓq ((Nat.prime_dvd_prime_iff_eq hℓp Fact.out).mp h)
        · exact hℓq' ((Nat.prime_dvd_prime_iff_eq hℓp Fact.out).mp h)
      obtain ⟨α, β, h1, h2, -, -, -, h6, h7, -, -, h10⟩ :=
        CerednikDrinfeld.exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one
          hN hqN hq'N hqq' hq'5 hdef Λ R hΛ hR hRΛ n hn hS hnorm hsq ℓ hℓ3 s hs hR' n' hn' hS' hnorm' hsq' hnn' hsn'
      refine ⟨α, β, h1, h2, trivial, trivial, trivial, h6, h7, trivial, trivial, fun x => ?_⟩
      rw [CerednikDrinfeld.pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_primeHeckeSet_mulVec_of_degTotal_eq
        hN hqN hq'N hqq' hq'5 hdef Λ R hΛ hR hRΛ n hn hS hnorm hsq ℓ hℓ3 s hs hR' n' hn' hS' hnorm' hsq' hnn' hsn' α β h2 h7 h10 x]
      congr 1
      simp only [classSetHeckeData, dif_pos hlaws, classSetEdgeHecke, if_neg hℓq, if_neg hℓN]

  have hdegeq : ∀ c, (μ₁.deg (eE'' c) : ℕ) = (β.deg c : ℕ) := by
    intro c
    have A := congrArg (fun t : ℕ+ => (t : ℕ)) (μ₁.w_mapE (eE'' c))
    have B := congrArg (fun t : ℕ+ => (t : ℕ)) (β.w_mapE c)
    simp only [PNat.mul_coe] at A B
    rw [h₁, hw, hw''] at A
    rw [hβ] at B
    have hpos : 0 < (((classSetDegeneracyData (meetOrder R s) n').w c : ℕ+) : ℕ) := PNat.pos _
    exact Nat.eq_of_mul_eq_mul_right hpos (A.symm.trans B)

  apply Subtype.ext
  funext c
  rw [he]
  show (CerednikDrinfeld.pushforward μ₀.mapE (μ₁.pullbackFun (e.symm z : ↥(ribbonKernel D))) : E → ℤ) (eE c) =
    (((classSetHeckeData N q Λ R n).T ⟨ℓ, hℓp⟩).mulVecLin (z : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ)) c
  rw [Matrix.mulVecLin_apply, ← hdict, CerednikDrinfeld.pushforward_apply_eq_sum_filter,
    CerednikDrinfeld.pushforward_apply_eq_sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Fintype.sum_equiv eE'' (fun c'' => if μ₀.mapE (eE'' c'') = eE c then μ₁.pullbackFun ((e.symm z : ↥(ribbonKernel D)) : E → ℤ) (eE'' c'') else 0)
    (fun e'' => if μ₀.mapE e'' = eE c then μ₁.pullbackFun ((e.symm z : ↥(ribbonKernel D)) : E → ℤ) e'' else 0) (fun _ => rfl)]
  refine Finset.sum_congr rfl fun c'' _ => ?_
  have hβc : β.mapE c'' = ClassSet.mk _ (c''.out * s) := by rw [hβ]
  have hαc : α.mapE c'' = classSetForget _ _ c'' := by rw [hα]
  simp only [h₀, EmbeddingLike.apply_eq_iff_eq, hαc, DegeneracyData.FiniteHom.pullbackFun_apply]
  split_ifs with hc
  · rw [h₁, hy, hβc, hdegeq]
  · rfl

end S_CerednikDrinfeld_pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq (solution)
