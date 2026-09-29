-- Prove2me | solution 1 for DrinfeldCurve.two_mul_genusFF_fixedField_rootsOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1035e782-41b2-5854-95c2-2c8efa65f2db

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_minpoly_eq_X_pow_sub_C_of_isCoprime_apply
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_finrankAlong_eq_of_pow_eq_X_sub_X_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_two_mul_genusFF_fixedField_rootsOfUnity
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left"

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_mu drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective x y relation natCard_rootsOfUnity_galoisField_two scalarOf muAction muAction_x muAction_y one_mem_hSubgroup_of_mem"
p2m_open "DrinfeldCurve"
namespace GenusAux
p2m_open "AlgebraicCurve~genus Polynomial"

section Presentation

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

theorem charP_of_galoisField : CharP k q := charP_of_injective_algebraMap' (GaloisField q 2) q

theorem two_le_q : 2 ≤ q := (Fact.out : q.Prime).two_le

theorem one_lt_q : 1 < q := (Fact.out : q.Prime).one_lt

theorem cast_q_eq_zero : (q : k) = 0 := by
  haveI := charP_of_galoisField q k
  exact CharP.cast_eq_zero k q

theorem cast_q_add_one_ne_zero : ((q + 1 : ℕ) : k) ≠ 0 := by
  rw [Nat.cast_add, cast_q_eq_zero q k, zero_add, Nat.cast_one]
  exact one_ne_zero

noncomputable def xF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)

noncomputable def yF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)

theorem relF : xF q k * yF q k ^ q - xF q k ^ q * yF q k = 1 := by
  have h := congrArg (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) (relation q k)
  simpa only [xF, yF, map_sub, map_mul, map_pow, map_one] using h

theorem yF_ne_zero : yF q k ≠ 0 := by
  intro h
  have h1 := relF q k
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rw [h, zero_pow hq, mul_zero, mul_zero, sub_zero] at h1
  exact zero_ne_one h1

theorem xF_ne_zero : xF q k ≠ 0 := by
  intro h
  have h1 := relF q k
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rw [h, zero_pow hq, zero_mul, zero_mul, sub_zero] at h1
  exact zero_ne_one h1

noncomputable def uFF : drinfeldFunctionField q k :=
  algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) /
    algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)

noncomputable def wFF : drinfeldFunctionField q k :=
  (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k))⁻¹

theorem uFF_def : uFF q k = xF q k / yF q k := rfl

theorem wFF_def : wFF q k = (yF q k)⁻¹ := rfl

theorem wFF_ne_zero : wFF q k ≠ 0 := by
  rw [wFF_def]; exact inv_ne_zero (yF_ne_zero q k)

theorem uFF_ne_zero : uFF q k ≠ 0 := by
  rw [uFF_def]; exact div_ne_zero (xF_ne_zero q k) (yF_ne_zero q k)

theorem xF_eq : xF q k = uFF q k / wFF q k := by
  rw [uFF_def, wFF_def, div_inv_eq_mul, div_mul_cancel₀ _ (yF_ne_zero q k)]

theorem yF_eq : yF q k = (wFF q k)⁻¹ := by
  rw [wFF_def, inv_inv]

theorem wFF_pow : wFF q k ^ (q + 1) = uFF q k - uFF q k ^ q := by
  have hy := yF_ne_zero q k
  have h := relF q k

  have h1 : yF q k ^ q * (yF q k)⁻¹ ^ (q + 1) = (yF q k)⁻¹ := by
    rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hy, one_pow, one_mul]
  have h2 : yF q k * (yF q k)⁻¹ ^ (q + 1) = (yF q k)⁻¹ ^ q := by
    rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
  calc wFF q k ^ (q + 1) = 1 * (yF q k)⁻¹ ^ (q + 1) := by rw [wFF_def, one_mul]
    _ = (xF q k * yF q k ^ q - xF q k ^ q * yF q k) * (yF q k)⁻¹ ^ (q + 1) := by rw [h]
    _ = xF q k * (yF q k ^ q * (yF q k)⁻¹ ^ (q + 1)) - xF q k ^ q * (yF q k * (yF q k)⁻¹ ^ (q + 1)) := by ring
    _ = uFF q k - uFF q k ^ q := by rw [h1, h2, uFF_def, div_eq_mul_inv, mul_pow]

theorem uFF_sub_pow_ne_zero : uFF q k - uFF q k ^ q ≠ 0 := by
  rw [← wFF_pow]
  exact pow_ne_zero _ (wFF_ne_zero q k)

theorem q_add_one_le_totalDegree : q + 1 ≤ (drinfeldPoly q k - 1).totalDegree := by
  classical
  have hq1 : q ≠ 1 := (Fact.out : q.Prime).one_lt.ne'
  let s : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 q
  have hcoeff : MvPolynomial.coeff s (drinfeldPoly q k - 1) = 1 := by
    rw [drinfeldPoly, MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
    have h1 : MvPolynomial.coeff s (MvPolynomial.X (R := k) 0 * MvPolynomial.X 1 ^ q) = 1 := by
      have : (MvPolynomial.X (R := k) (0 : Fin 2) * MvPolynomial.X 1 ^ q) = MvPolynomial.monomial s 1 := by
        rw [MvPolynomial.X, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
      rw [this, MvPolynomial.coeff_monomial, if_pos rfl]
    have h2 : MvPolynomial.coeff s (MvPolynomial.X (R := k) 0 ^ q * MvPolynomial.X 1) = 0 := by
      have : (MvPolynomial.X (R := k) (0 : Fin 2) ^ q * MvPolynomial.X 1) =
          MvPolynomial.monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
        rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
      rw [this, MvPolynomial.coeff_monomial, if_neg]
      intro hs
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hs
      simp [s] at this
      exact hq1 this
    have h3 : (if (0 : Fin 2 →₀ ℕ) = s then (1 : k) else 0) = 0 := by
      rw [if_neg]
      intro hs
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hs
      simp [s] at this
    rw [h1, h2, h3, sub_zero, sub_zero]
  have hs : s ∈ (drinfeldPoly q k - 1).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact one_ne_zero
  have := MvPolynomial.le_totalDegree hs
  have hsum : (s.sum fun _ e => e) = q + 1 := by
    simp [s, Finsupp.sum_add_index', add_comm]
  rw [hsum] at this
  exact this

theorem transcendental_uFF : Transcendental k (uFF q k) := by
  classical
  intro halg

  have hint : IsIntegral k (uFF q k) := halg.isIntegral
  have hdeg : (minpoly k (uFF q k)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k (uFF q k) hdeg

  have hxy : xF q k = algebraMap k (drinfeldFunctionField q k) c * yF q k := by
    rw [hc, uFF_def, div_mul_cancel₀ _ (yF_ne_zero q k)]
  have hinj : Function.Injective (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) :=
    IsFractionRing.injective (CoordRing q k) (drinfeldFunctionField q k)
  have hxy' : x q k = algebraMap k (CoordRing q k) c * y q k := by
    apply hinj
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact hxy

  have hmem : (MvPolynomial.X 0 - MvPolynomial.C c * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ drinfeldIdeal q k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hC : mk q k (MvPolynomial.C c) = algebraMap k (CoordRing q k) c := (mk q k).commutes c
    have : mk q k (MvPolynomial.X 0 - MvPolynomial.C c * MvPolynomial.X 1) = x q k - algebraMap k (CoordRing q k) c * y q k := by
      rw [map_sub, map_mul, hC]; rfl
    change mk q k _ = 0
    rw [this, hxy', sub_self]
  rw [drinfeldIdeal, Ideal.mem_span_singleton] at hmem

  have hne : (MvPolynomial.X 0 - MvPolynomial.C c * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ≠ 0 := by
    intro h0
    have := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h0
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_same, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
      if_neg, mul_zero, sub_zero, MvPolynomial.coeff_zero] at this
    · exact one_ne_zero this
    · intro h01
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h01
      simp at this
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hmem hne
  have hle' : (MvPolynomial.X 0 - MvPolynomial.C c * MvPolynomial.X 1 : MvPolynomial (Fin 2) k).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (MvPolynomial.totalDegree_X _).le ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_X _).le
  have h3 := q_add_one_le_totalDegree q k
  have h2 := two_le_q q
  omega

theorem aeval_uFF_injective : Function.Injective (Polynomial.aeval (R := k) (uFF q k)) :=
  transcendental_iff_injective.mp (transcendental_uFF q k)

noncomputable def phi : RatFunc k →ₐ[k] drinfeldFunctionField q k :=
  RatFunc.liftAlgHom (Polynomial.aeval (uFF q k))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_uFF_injective q k))

theorem phi_injective : Function.Injective (phi q k) :=
  RatFunc.liftAlgHom_injective _ (aeval_uFF_injective q k)

theorem phi_algebraMap (p : k[X]) : phi q k (algebraMap k[X] (RatFunc k) p) = Polynomial.aeval (uFF q k) p := by
  have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (R := k) (uFF q k))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_uFF_injective q k)) p 1
  rw [map_one, map_one, div_one, div_one] at h
  exact h

@[scoped simp] theorem phi_X : phi q k RatFunc.X = uFF q k := by
  rw [← RatFunc.algebraMap_X, phi_algebraMap, Polynomial.aeval_X]

@[scoped simp] theorem phi_C (c : k) : phi q k (RatFunc.C c) = algebraMap k (drinfeldFunctionField q k) c := by
  rw [← RatFunc.algebraMap_C, phi_algebraMap, Polynomial.aeval_C]

theorem phi_X_sub_X_pow : phi q k (RatFunc.X - RatFunc.X ^ q) = wFF q k ^ (q + 1) := by
  rw [map_sub, map_pow, phi_X, wFF_pow]

noncomputable scoped instance algRatFunc : Algebra (RatFunc k) (drinfeldFunctionField q k) := (phi q k).toRingHom.toAlgebra

theorem algebraMap_ratFunc_eq : algebraMap (RatFunc k) (drinfeldFunctionField q k) = (phi q k).toRingHom := rfl

theorem algebraMap_ratFunc_apply (f : RatFunc k) : algebraMap (RatFunc k) (drinfeldFunctionField q k) f = phi q k f := rfl

scoped instance isScalarTower_ratFunc : IsScalarTower k (RatFunc k) (drinfeldFunctionField q k) :=
  AlgebraicCurve.isScalarTower_along (phi q k)

theorem algebraAlong_phi_eq : AlgebraicCurve.algebraAlong (phi q k) = algRatFunc q k := rfl

theorem algebraMap_coordRing_mem_adjoin (a : CoordRing q k) :
    algebraMap (CoordRing q k) (drinfeldFunctionField q k) a ∈
      IntermediateField.adjoin (RatFunc k) ({wFF q k} : Set (drinfeldFunctionField q k)) := by
  set E := IntermediateField.adjoin (RatFunc k) ({wFF q k} : Set (drinfeldFunctionField q k)) with hE
  have hw : wFF q k ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hu : uFF q k ∈ E := by
    have : uFF q k = algebraMap (RatFunc k) (drinfeldFunctionField q k) RatFunc.X := by
      rw [algebraMap_ratFunc_apply, phi_X]
    rw [this]
    exact E.algebraMap_mem _
  have hy : yF q k ∈ E := by
    rw [yF_eq]
    exact E.inv_mem hw
  have hx : xF q k ∈ E := by
    rw [xF_eq]
    exact E.div_mem hu hw
  obtain ⟨p, rfl⟩ := mk_surjective q k a
  induction p using MvPolynomial.induction_on with
  | C c =>
    have : mk q k (MvPolynomial.C c) = algebraMap k (CoordRing q k) c := (mk q k).commutes c
    rw [this, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k (RatFunc k) (drinfeldFunctionField q k)]
    exact E.algebraMap_mem _
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact E.add_mem h₁ h₂
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine E.mul_mem hp ?_
    fin_cases i
    · exact hx
    · exact hy

theorem adjoin_wFF_eq_top :
    IntermediateField.adjoin (RatFunc k) ({wFF q k} : Set (drinfeldFunctionField q k)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := CoordRing q k) z
  exact IntermediateField.div_mem _ (algebraMap_coordRing_mem_adjoin q k a) (algebraMap_coordRing_mem_adjoin q k b)

theorem closure_range_phi_eq_top : Subfield.closure (Set.range (phi q k) ∪ {wFF q k}) = ⊤ := by
  have h := congrArg IntermediateField.toSubfield (adjoin_wFF_eq_top q k)
  rw [IntermediateField.adjoin_toSubfield] at h
  exact h

theorem X_sub_X_pow_ne_zero : (RatFunc.X - RatFunc.X ^ q : RatFunc k) ≠ 0 := by
  intro h
  have := congrArg (phi q k) h
  rw [phi_X_sub_X_pow, map_zero] at this
  exact pow_ne_zero _ (wFF_ne_zero q k) this

theorem natDegree_X_sub_X_pow : (Polynomial.X - Polynomial.X ^ q : k[X]).natDegree = q := by
  have hq := one_lt_q q
  rw [sub_eq_neg_add, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]
  · rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    exact hq

theorem intDegree_X_sub_X_pow : RatFunc.intDegree (RatFunc.X - RatFunc.X ^ q : RatFunc k) = q := by
  have : (RatFunc.X - RatFunc.X ^ q : RatFunc k) = algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.X ^ q) := by
    rw [map_sub, map_pow, RatFunc.algebraMap_X]
  rw [this, RatFunc.intDegree_polynomial, natDegree_X_sub_X_pow]

theorem isCoprime_q_succ : IsCoprime (q : ℤ) ((q + 1 : ℕ) : ℤ) :=
  ⟨-1, 1, by push_cast; ring⟩

theorem minpoly_wFF : minpoly (RatFunc k) (wFF q k) = X ^ (q + 1) - C (RatFunc.X - RatFunc.X ^ q) := by
  have hv : ∀ a b : RatFunc k, a ≠ 0 → b ≠ 0 → RatFunc.intDegree (a * b) = RatFunc.intDegree a + RatFunc.intDegree b :=
    fun a b ha hb => RatFunc.intDegree_mul ha hb
  have hcop : IsCoprime (RatFunc.intDegree (RatFunc.X - RatFunc.X ^ q : RatFunc k)) ((q + 1 : ℕ) : ℤ) := by
    rw [intDegree_X_sub_X_pow]
    exact isCoprime_q_succ q
  have hθ : wFF q k ^ (q + 1) = algebraMap (RatFunc k) (drinfeldFunctionField q k) (RatFunc.X - RatFunc.X ^ q) := by
    rw [algebraMap_ratFunc_apply, phi_X_sub_X_pow]
  exact minpoly.eq_X_pow_sub_C_of_isCoprime_apply (L := drinfeldFunctionField q k) RatFunc.intDegree hv
    (Nat.succ_pos q) (X_sub_X_pow_ne_zero q k) hcop (wFF q k) hθ

theorem isIntegral_wFF : IsIntegral (RatFunc k) (wFF q k) := by
  refine ⟨X ^ (q + 1) - C (RatFunc.X - RatFunc.X ^ q), Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero q), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, algebraMap_ratFunc_apply, phi_X_sub_X_pow, sub_self]

theorem natDegree_minpoly_wFF : (minpoly (RatFunc k) (wFF q k)).natDegree = q + 1 := by
  rw [minpoly_wFF, Polynomial.natDegree_X_pow_sub_C]

scoped instance finiteDimensional_ratFunc : FiniteDimensional (RatFunc k) (drinfeldFunctionField q k) := by
  have h : FiniteDimensional (RatFunc k) (IntermediateField.adjoin (RatFunc k) ({wFF q k} : Set (drinfeldFunctionField q k))) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_wFF q k)
  rw [adjoin_wFF_eq_top] at h
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := RatFunc k) (E := drinfeldFunctionField q k)).toLinearEquiv

theorem finrank_ratFunc : Module.finrank (RatFunc k) (drinfeldFunctionField q k) = q + 1 := by
  rw [← IntermediateField.finrank_top', ← adjoin_wFF_eq_top, IntermediateField.adjoin.finrank (isIntegral_wFF q k),
    natDegree_minpoly_wFF]

theorem cast_q_add_one_ne_zero_ratFunc : ((q + 1 : ℕ) : RatFunc k) ≠ 0 := by
  intro h
  apply cast_q_add_one_ne_zero q k
  have := congrArg (phi q k) h
  rwa [map_natCast, map_zero, ← map_natCast (algebraMap k (drinfeldFunctionField q k)), map_eq_zero] at this

theorem isSeparable_wFF : IsSeparable (RatFunc k) (wFF q k) := by
  rw [IsSeparable, minpoly_wFF]
  exact Polynomial.separable_X_pow_sub_C _ (cast_q_add_one_ne_zero_ratFunc q k) (X_sub_X_pow_ne_zero q k)

scoped instance isSeparable_ratFunc : Algebra.IsSeparable (RatFunc k) (drinfeldFunctionField q k) := by
  have h : Algebra.IsSeparable (RatFunc k) (IntermediateField.adjoin (RatFunc k) ({wFF q k} : Set (drinfeldFunctionField q k))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc k) (drinfeldFunctionField q k)).mpr
      (isSeparable_wFF q k)
  rw [adjoin_wFF_eq_top] at h
  exact Algebra.IsSeparable.of_algHom (RatFunc k) _
    (IntermediateField.topEquiv (F := RatFunc k) (E := drinfeldFunctionField q k)).symm.toAlgHom

theorem finiteAlong_phi : AlgebraicCurve.FiniteAlong k (phi q k) := finiteDimensional_ratFunc q k

theorem separableAlong_phi : AlgebraicCurve.SeparableAlong k (phi q k) := isSeparable_ratFunc q k

theorem finrankAlong_phi : AlgebraicCurve.finrankAlong k (phi q k) = q + 1 := finrank_ratFunc q k

theorem phi_isIntegral : (phi q k).toRingHom.IsIntegral := fun z =>
  (IsIntegral.of_finite (RatFunc k) z)

end Presentation

section QuotientPresentation

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

theorem scalarOf_one' : scalarOf q k 1 = 1 := by simp [scalarOf]

theorem scalarOf_mul' (ζ η : (GaloisField q 2)ˣ) : scalarOf q k (ζ * η) = scalarOf q k ζ * scalarOf q k η := by
  simp [scalarOf]

theorem scalarOf_ne_zero (ζ : (GaloisField q 2)ˣ) : scalarOf q k ζ ≠ 0 := by
  simp [scalarOf]

theorem scalarOf_eq_one_iff (ζ : (GaloisField q 2)ˣ) : scalarOf q k ζ = 1 ↔ ζ = 1 := by
  rw [scalarOf, ← (algebraMap (GaloisField q 2) k).map_one, (algebraMap (GaloisField q 2) k).injective.eq_iff,
    Units.val_eq_one]

noncomputable def muF : rootsOfUnity (q + 1) (GaloisField q 2) →* (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) where
  toFun ζ := IsFractionRing.algEquivOfAlgEquiv (muAction q k ζ)
  map_one' := by
    apply AlgEquiv.ext
    intro z
    have key : ((IsFractionRing.algEquivOfAlgEquiv (muAction q k 1) :
          drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k) = RingHom.id _ := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
      ext a
      simp [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    simpa using RingHom.congr_fun key z
  map_mul' ζ η := by
    apply AlgEquiv.ext
    intro z
    have key : ((IsFractionRing.algEquivOfAlgEquiv (muAction q k (ζ * η)) :
          drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k) =
        ((IsFractionRing.algEquivOfAlgEquiv (muAction q k ζ) :
          drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp
          ((IsFractionRing.algEquivOfAlgEquiv (muAction q k η) :
            drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
              drinfeldFunctionField q k →+* drinfeldFunctionField q k) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
      ext a
      simp [IsFractionRing.algEquivOfAlgEquiv_algebraMap, map_mul]
    simpa using RingHom.congr_fun key z

theorem muF_apply (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    muF q k ζ = IsFractionRing.algEquivOfAlgEquiv (muAction q k ζ) := rfl

theorem muF_algebraMap (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) (a : CoordRing q k) :
    muF q k ζ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) a) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (muAction q k ζ a) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (muAction q k ζ) a

noncomputable def sF (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : drinfeldFunctionField q k :=
  algebraMap k (drinfeldFunctionField q k) (scalarOf q k ζ)

theorem sF_ne_zero (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : sF q k ζ ≠ 0 :=
  (_root_.map_ne_zero (algebraMap k (drinfeldFunctionField q k))).mpr (scalarOf_ne_zero q k ζ)

theorem muF_xF (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : muF q k ζ (xF q k) = sF q k ζ * xF q k := by
  rw [xF, muF_algebraMap, muAction_x, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem muF_yF (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : muF q k ζ (yF q k) = sF q k ζ * yF q k := by
  rw [yF, muF_algebraMap, muAction_y, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem muF_uFF (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : muF q k ζ (uFF q k) = uFF q k := by
  rw [uFF_def, map_div₀, muF_xF, muF_yF, mul_div_mul_left _ _ (sF_ne_zero q k ζ)]

theorem muF_wFF (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : muF q k ζ (wFF q k) = (sF q k ζ)⁻¹ * wFF q k := by
  rw [wFF_def, map_inv₀, muF_yF, mul_inv]

theorem muF_wFF_pow (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) (j : ℕ) :
    muF q k ζ (wFF q k ^ j) = (sF q k ζ)⁻¹ ^ j * wFF q k ^ j := by
  rw [map_pow, muF_wFF, mul_pow]

theorem muF_injective : Function.Injective (muF q k) := by
  rw [injective_iff_map_eq_one]
  intro ζ hζ
  have h := congrArg (fun σ => σ (yF q k)) hζ
  simp only [AlgEquiv.one_apply] at h
  rw [muF_yF] at h
  have h1 : sF q k ζ = 1 := by
    have := mul_right_cancel₀ (yF_ne_zero q k) (h.trans (one_mul _).symm)
    exact this
  rw [sF, ← (algebraMap k (drinfeldFunctionField q k)).map_one, (algebraMap k _).injective.eq_iff,
    scalarOf_eq_one_iff] at h1
  exact Subtype.ext h1

variable (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))

theorem scalarOf_pow_natCard {ζ : rootsOfUnity (q + 1) (GaloisField q 2)} (hζ : ζ ∈ C) :
    scalarOf q k ζ ^ Nat.card C = 1 := by
  have h : (⟨ζ, hζ⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
  have h' : ζ ^ Nat.card C = 1 := by
    have := congrArg Subtype.val h
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
  have h'' : ((ζ : (GaloisField q 2)ˣ)) ^ Nat.card C = 1 := by
    have := congrArg Subtype.val h'
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
  rw [scalarOf, ← map_pow, ← Units.val_pow_eq_pow_val, h'', Units.val_one, map_one]

theorem sF_pow_natCard {ζ : rootsOfUnity (q + 1) (GaloisField q 2)} (hζ : ζ ∈ C) : sF q k ζ ^ Nat.card C = 1 := by
  rw [sF, ← map_pow, scalarOf_pow_natCard q k C hζ, map_one]

theorem muF_wFF_pow_natCard {ζ : rootsOfUnity (q + 1) (GaloisField q 2)} (hζ : ζ ∈ C) :
    muF q k ζ (wFF q k ^ Nat.card C) = wFF q k ^ Nat.card C := by
  rw [muF_wFF_pow, inv_pow, sF_pow_natCard q k C hζ, inv_one, one_mul]

noncomputable def GC : Subgroup (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) := C.map (muF q k)

noncomputable def EC : IntermediateField k (drinfeldFunctionField q k) := IntermediateField.fixedField (GC q k C)

theorem mem_EC_iff (z : drinfeldFunctionField q k) : z ∈ EC q k C ↔ ∀ ζ ∈ C, muF q k ζ z = z := by
  rw [EC, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h ζ hζ
    exact h (muF q k ζ) (Subgroup.mem_map_of_mem _ hζ)
  · rintro h σ ⟨ζ, hζ, rfl⟩
    exact h ζ hζ

theorem uFF_mem_EC : uFF q k ∈ EC q k C :=
  (mem_EC_iff q k C _).mpr fun ζ _ => muF_uFF q k ζ

theorem wFF_pow_natCard_mem_EC : wFF q k ^ Nat.card C ∈ EC q k C :=
  (mem_EC_iff q k C _).mpr fun _ hζ => muF_wFF_pow_natCard q k C hζ

theorem natCard_GC : Nat.card (GC q k C) = Nat.card C :=
  Subgroup.card_map_of_injective (muF_injective q k)

scoped instance finite_GC : Finite (GC q k C) :=
  Finite.of_surjective (fun c : C => (⟨muF q k c, Subgroup.mem_map_of_mem _ c.2⟩ : GC q k C)) (by
    rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩)

theorem finrank_EC : Module.finrank (EC q k C) (drinfeldFunctionField q k) = Nat.card C := by
  haveI := Fintype.ofFinite (GC q k C)
  rw [← natCard_GC q k C, Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card (GC q k C) (drinfeldFunctionField q k)

theorem natCard_C_dvd : Nat.card C ∣ q + 1 := by
  have h := Subgroup.card_subgroup_dvd_card C
  rwa [natCard_rootsOfUnity_galoisField_two q] at h

theorem natCard_C_pos : 0 < Nat.card C := Nat.card_pos

theorem div_mul_natCard : (q + 1) / Nat.card C * Nat.card C = q + 1 :=
  Nat.div_mul_cancel (natCard_C_dvd q C)

theorem div_natCard_pos : 0 < (q + 1) / Nat.card C :=
  Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos q) (natCard_C_dvd q C)) (natCard_C_pos q C)

theorem muF_phi (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) (f : RatFunc k) : muF q k ζ (phi q k f) = phi q k f := by
  have key : ((muF q k ζ : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
        drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp (phi q k).toRingHom = (phi q k).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    refine RingHom.ext fun p => ?_
    show muF q k ζ (phi q k (algebraMap k[X] (RatFunc k) p)) = phi q k (algebraMap k[X] (RatFunc k) p)
    rw [phi_algebraMap]
    simpa [muF_uFF] using
      (Polynomial.aeval_algHom_apply (muF q k ζ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)
        (uFF q k) p).symm
  exact RingHom.congr_fun key f

theorem phi_mem_EC (f : RatFunc k) : phi q k f ∈ EC q k C :=
  (mem_EC_iff q k C _).mpr fun ζ _ => muF_phi q k ζ f

noncomputable def phiC : RatFunc k →ₐ[k] EC q k C :=
  (phi q k).codRestrict (EC q k C).toSubalgebra (phi_mem_EC q k C)

@[scoped simp] theorem coe_phiC (f : RatFunc k) : (phiC q k C f : drinfeldFunctionField q k) = phi q k f := rfl

theorem val_comp_phiC : (EC q k C).val.comp (phiC q k C) = phi q k := rfl

theorem phiC_X : phiC q k C RatFunc.X = ⟨uFF q k, uFF_mem_EC q k C⟩ :=
  Subtype.ext (phi_X q k)

theorem phiC_injective : Function.Injective (phiC q k C) := fun a b h =>
  phi_injective q k (congrArg Subtype.val h)

noncomputable def cC : EC q k C := ⟨wFF q k ^ Nat.card C, wFF_pow_natCard_mem_EC q k C⟩

@[scoped simp] theorem coe_cC : (cC q k C : drinfeldFunctionField q k) = wFF q k ^ Nat.card C := rfl

theorem cC_ne_zero : cC q k C ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  rw [coe_cC, ZeroMemClass.coe_zero] at this
  exact pow_ne_zero _ (wFF_ne_zero q k) this

theorem phiC_X_sub_X_pow : phiC q k C (RatFunc.X - RatFunc.X ^ q) = cC q k C ^ ((q + 1) / Nat.card C) := by
  apply Subtype.ext
  rw [coe_phiC, phi_X_sub_X_pow, SubmonoidClass.coe_pow, coe_cC, ← pow_mul, mul_comm, div_mul_natCard q C]

noncomputable scoped instance algRatFuncEC : Algebra (RatFunc k) (EC q k C) := (phiC q k C).toRingHom.toAlgebra

theorem algebraMap_ratFunc_EC_apply (f : RatFunc k) : algebraMap (RatFunc k) (EC q k C) f = phiC q k C f := rfl

scoped instance isScalarTower_ratFunc_EC : IsScalarTower k (RatFunc k) (EC q k C) :=
  AlgebraicCurve.isScalarTower_along (phiC q k C)

scoped instance isScalarTower_ratFunc_EC_F : IsScalarTower (RatFunc k) (EC q k C) (drinfeldFunctionField q k) :=
  IsScalarTower.of_algebraMap_eq fun f => rfl

scoped instance finiteDimensional_ratFunc_EC : FiniteDimensional (RatFunc k) (EC q k C) :=
  FiniteDimensional.of_injective (IsScalarTower.toAlgHom (RatFunc k) (EC q k C) (drinfeldFunctionField q k)).toLinearMap
    (RingHom.injective _)

scoped instance isSeparable_ratFunc_EC : Algebra.IsSeparable (RatFunc k) (EC q k C) :=
  Algebra.isSeparable_tower_bot_of_isSeparable (RatFunc k) (EC q k C) (drinfeldFunctionField q k)

theorem finrank_ratFunc_EC : Module.finrank (RatFunc k) (EC q k C) = (q + 1) / Nat.card C := by
  have h := Module.finrank_mul_finrank (RatFunc k) (EC q k C) (drinfeldFunctionField q k)
  rw [finrank_EC, finrank_ratFunc] at h
  exact Nat.eq_div_of_mul_eq_left (natCard_C_pos q C).ne' h

theorem finiteAlong_phiC : AlgebraicCurve.FiniteAlong k (phiC q k C) := finiteDimensional_ratFunc_EC q k C

theorem separableAlong_phiC : AlgebraicCurve.SeparableAlong k (phiC q k C) := isSeparable_ratFunc_EC q k C

theorem finrankAlong_phiC : AlgebraicCurve.finrankAlong k (phiC q k C) = (q + 1) / Nat.card C := finrank_ratFunc_EC q k C

theorem phiC_isIntegral : (phiC q k C).toRingHom.IsIntegral := fun z => IsIntegral.of_finite (RatFunc k) z

theorem isCoprime_q_div_natCard : IsCoprime (q : ℤ) (((q + 1) / Nat.card C : ℕ) : ℤ) := by
  rw [Nat.isCoprime_iff_coprime]
  have h1 : Nat.Coprime q (q + 1) := by simp
  exact h1.coprime_dvd_right ⟨Nat.card C, (div_mul_natCard q C).symm⟩

theorem minpoly_cC :
    minpoly (RatFunc k) (cC q k C) = X ^ ((q + 1) / Nat.card C) - Polynomial.C (RatFunc.X - RatFunc.X ^ q) := by
  have hv : ∀ a b : RatFunc k, a ≠ 0 → b ≠ 0 → RatFunc.intDegree (a * b) = RatFunc.intDegree a + RatFunc.intDegree b :=
    fun a b ha hb => RatFunc.intDegree_mul ha hb
  have hcop : IsCoprime (RatFunc.intDegree (RatFunc.X - RatFunc.X ^ q : RatFunc k)) (((q + 1) / Nat.card C : ℕ) : ℤ) := by
    rw [intDegree_X_sub_X_pow]
    exact isCoprime_q_div_natCard q C
  have hθ : cC q k C ^ ((q + 1) / Nat.card C) = algebraMap (RatFunc k) (EC q k C) (RatFunc.X - RatFunc.X ^ q) := by
    rw [algebraMap_ratFunc_EC_apply, phiC_X_sub_X_pow]
  exact minpoly.eq_X_pow_sub_C_of_isCoprime_apply (L := EC q k C) RatFunc.intDegree hv
    (div_natCard_pos q C) (X_sub_X_pow_ne_zero q k) hcop (cC q k C) hθ

theorem isIntegral_cC : IsIntegral (RatFunc k) (cC q k C) := IsIntegral.of_finite (RatFunc k) _

theorem adjoin_cC_eq_top : IntermediateField.adjoin (RatFunc k) ({cC q k C} : Set (EC q k C)) = ⊤ := by
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  rw [IntermediateField.adjoin.finrank (isIntegral_cC q k C), IntermediateField.finrank_top', finrank_ratFunc_EC,
    minpoly_cC, Polynomial.natDegree_X_pow_sub_C]

theorem closure_range_phiC_eq_top : Subfield.closure (Set.range (phiC q k C) ∪ {cC q k C}) = ⊤ := by
  have h := congrArg IntermediateField.toSubfield (adjoin_cC_eq_top q k C)
  rw [IntermediateField.adjoin_toSubfield] at h
  exact h

end QuotientPresentation

section QuotientGenus
variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))

theorem coprime_q_div_natCard : q.Coprime ((q + 1) / Nat.card C) :=
  Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (natCard_C_dvd q C))
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right q))

theorem cast_div_natCard_ne_zero : (((q + 1) / Nat.card C : ℕ) : k) ≠ 0 := by
  intro h
  apply cast_q_add_one_ne_zero q k
  rw [← div_mul_natCard q C, Nat.cast_mul, h, zero_mul]

theorem genusFF_EC :
    genusFF k (EC q k C) = ((q + 1) / Nat.card C - 1) * (q - 1) / 2 := by
  haveI := charP_of_galoisField q k
  exact AlgebraicCurve.genusFF_eq_of_finrankAlong_eq_of_pow_eq_X_sub_X_pow q ((q + 1) / Nat.card C)
    (cast_div_natCard_ne_zero q k C) (coprime_q_div_natCard q C) (phiC q k C) (finiteAlong_phiC q k C)
    (separableAlong_phiC q k C) (finrankAlong_phiC q k C) (cC q k C) (phiC_X_sub_X_pow q k C)
    (closure_range_phiC_eq_top q k C)

end QuotientGenus

section Adapter
variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

theorem hFunctionFieldAction_one_eq_muF (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩ = muF q k ζ := by
  rw [hFunctionFieldAction_mu]
  rfl

theorem closure_range_hFunctionFieldAction_eq_GC (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    Subgroup.closure (Set.range fun ζ : C =>
        hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩) = GC q k C := by
  have hr : (Set.range fun ζ : C =>
      hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩) = (GC q k C : Set (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)) := by
    ext σ
    simp only [Set.mem_range, hFunctionFieldAction_one_eq_muF, GC, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨ζ, rfl⟩
      exact ⟨ζ, ζ.2, rfl⟩
    · rintro ⟨ζ, hζ, rfl⟩
      exact ⟨⟨ζ, hζ⟩, rfl⟩
  rw [hr, Subgroup.closure_eq]

theorem genusFF_fixedField_closure (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    AlgebraicCurve.genusFF k
        ↥(IntermediateField.fixedField (Subgroup.closure (Set.range fun ζ : C =>
            hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩))) =
      ((q + 1) / Nat.card C - 1) * (q - 1) / 2 := by
  rw [closure_range_hFunctionFieldAction_eq_GC]
  exact genusFF_EC q k C

theorem even_sub_one_mul_sub_one {n : ℕ} (hqn : q.Coprime n) : Even ((n - 1) * (q - 1)) := by
  by_cases h2 : q = 2
  · subst h2
    have hn : Odd n := Nat.Coprime.odd_of_left hqn
    exact (Nat.Odd.sub_odd hn odd_one).mul_right _
  · exact (Nat.Odd.sub_odd ((Fact.out : q.Prime).odd_of_ne_two h2) odd_one).mul_left _

theorem two_mul_genusFF_fixedField_closure (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (d : ℕ) (hd : d * Nat.card C = q + 1) :
    2 * AlgebraicCurve.genusFF k
        ↥(IntermediateField.fixedField (Subgroup.closure (Set.range fun ζ : C =>
            hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩))) =
      (d - 1) * (q - 1) := by
  have hdC : d = (q + 1) / Nat.card C := (Nat.div_eq_of_eq_mul_left (natCard_C_pos q C) hd.symm).symm
  rw [genusFF_fixedField_closure q k C, hdC]
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_sub_one_mul_sub_one q (coprime_q_div_natCard q C)))

end Adapter

end GenusAux
p2m_reactivate "P2MW.S_DrinfeldCurve_two_mul_genusFF_fixedField_rootsOfUnity.DrinfeldCurve.GenusAux"
end DrinfeldCurve
p2m_reactivate "P2MW.S_DrinfeldCurve_two_mul_genusFF_fixedField_rootsOfUnity.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_two_mul_genusFF_fixedField_rootsOfUnity.DrinfeldCurve"

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_two_mul_genusFF_fixedField_rootsOfUnity.DrinfeldCurve in
theorem solution (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]
    [IsAlgClosed k] [IsDomain (CoordRing q k)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (d : ℕ) (hd : d * Nat.card C = q + 1) :
    2 * AlgebraicCurve.genusFF k
        ↥(IntermediateField.fixedField (Subgroup.closure (Set.range fun ζ : C =>
            hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩))) =
      (d - 1) * (q - 1) := by
  exact DrinfeldCurve.GenusAux.two_mul_genusFF_fixedField_closure q k C d hd

end S_DrinfeldCurve_two_mul_genusFF_fixedField_rootsOfUnity
end P2MW
export P2MW.S_DrinfeldCurve_two_mul_genusFF_fixedField_rootsOfUnity (solution)
