-- Prove2me | solution 1 for DrinfeldCurve.natCard_place_restrictAlong_eq_neg_one_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/be4f7cfa-d643-54ed-9196-1111b748c4a2

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_DrinfeldCurve_isCurveOver_drinfeldFunctionField
import Theorems.Thm_AlgebraicCurve_finsum_ramificationIndex_ratFunc_sub_one_eq_of_tame
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_minpoly_eq_X_pow_sub_C_of_isCoprime_apply
import Definitions.Def_AlgebraicCurve_Correspondence

import Theorems.Thm_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero
import Theorems.Thm_DrinfeldCurve_finite_and_ncard_setOf_twistedFrobenius_affineFixed
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_mu drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext mk_drinfeldPoly x y relation muAction muAction_x muAction_y one_mem_hSubgroup_of_mem isCurveOver_drinfeldFunctionField finite_and_ncard_setOf_twistedFrobenius_affineFixed"
p2m_open "DrinfeldCurve"

namespace GenusAux
open AlgebraicCurve Polynomial

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

private noncomputable def _root_.DrinfeldCurve.GenusAux.xF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)

p2m_export "DrinfeldCurve.GenusAux" "xF"

private noncomputable def _root_.DrinfeldCurve.GenusAux.yF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)

p2m_export "DrinfeldCurve.GenusAux" "yF"
theorem relF : xF q k * yF q k ^ q - xF q k ^ q * yF q k = 1 := by
  have h := congrArg (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) (relation q k)
  simp only [map_sub, map_mul, map_pow, map_one] at h
  exact h

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
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_same, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
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

section Generic

theorem card_fiber_eq_one_of_forall_ramificationIndex_eq
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (he : ∀ w ∈ v.fiber F', w.ramificationIndex F = Module.finrank F F') :
    (v.fiber F').card = 1 := by
  have hsum := AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank v hv hrat
  have hsum' : ∑ w ∈ v.fiber F', (Module.finrank F F' : ℤ) = Module.finrank F F' :=
    (Finset.sum_congr rfl fun w hw => by rw [he w hw]).trans hsum
  rw [Finset.sum_const, nsmul_eq_mul] at hsum'
  have hpos : (0 : ℤ) < Module.finrank F F' := by exact_mod_cast Module.finrank_pos
  have hcard : ((v.fiber F').card : ℤ) = 1 := Int.eq_one_of_mul_eq_self_left hpos.ne' hsum'
  exact_mod_cast hcard

theorem finsum_eq_sum_sum_fiber
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']
    (S : Finset (Place K F)) (g : Place K F' → ℤ) (hg : ∀ w, w.restrict F ∉ S → g w = 0) :
    ∑ᶠ w, g w = ∑ v ∈ S, ∑ w ∈ v.fiber F', g w := by
  classical
  have hsupp : Function.support g ⊆ ↑(S.biUnion fun v => v.fiber F') := by
    intro w hw
    rw [Function.mem_support] at hw
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨w.restrict F, ?_, Place.restrict_mem_fiber w⟩
    by_contra h
    exact hw (hg w h)
  rw [finsum_eq_sum_of_support_subset g hsupp, Finset.sum_biUnion]
  intro v₁ _ v₂ _ hne
  show Disjoint (v₁.fiber F') (v₂.fiber F')
  rw [Finset.disjoint_left]
  intro w h1 h2
  exact hne ((Place.mem_fiber.mp h1).symm.trans (Place.mem_fiber.mp h2))
end Generic

section Count

p2m_open "AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
open scoped Classical

set_option linter.unusedSectionVars false

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

noncomputable def P0 : k[X] := X - X ^ q

theorem natDegree_P0 : (P0 q k).natDegree = q := by
  have h1 : 1 < q := one_lt_q q
  rw [P0, natDegree_sub_eq_right_of_natDegree_lt] <;> simp [h1]

theorem P0_ne_zero : P0 q k ≠ 0 := by
  intro h
  have h1 := natDegree_P0 q k
  have h2 := one_lt_q q
  rw [h, natDegree_zero] at h1
  omega

theorem derivative_P0 : derivative (P0 q k) = 1 := by
  haveI := charP_of_galoisField q k
  rw [P0, derivative_sub, derivative_X, derivative_X_pow, CharP.cast_eq_zero k q, C_0, zero_mul, sub_zero]

theorem separable_P0 : (P0 q k).Separable := by
  rw [Polynomial.separable_def, derivative_P0]
  exact isCoprime_one_right

theorem rootMultiplicity_P0_le_one (a : k) : rootMultiplicity a (P0 q k) ≤ 1 := by
  rw [← count_roots]
  exact count_roots_le_one (separable_P0 q k) a

theorem rootMultiplicity_P0_of_isRoot {a : k} (ha : (P0 q k).IsRoot a) : rootMultiplicity a (P0 q k) = 1 :=
  le_antisymm (rootMultiplicity_P0_le_one q k a) ((rootMultiplicity_pos (P0_ne_zero q k)).mpr ha)

theorem rootMultiplicity_P0_of_not_isRoot {a : k} (ha : ¬ (P0 q k).IsRoot a) : rootMultiplicity a (P0 q k) = 0 :=
  rootMultiplicity_eq_zero ha

theorem card_roots_P0 : (P0 q k).roots.toFinset.card = q := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (separable_P0 q k)),
    ← (IsAlgClosed.splits (P0 q k)).natDegree_eq_card_roots, natDegree_P0]

noncomputable def u0 : RatFunc k := algebraMap k[X] (RatFunc k) (P0 q k)

theorem u0_eq : u0 q k = RatFunc.X - RatFunc.X ^ q := by
  rw [u0, P0, map_sub, map_pow, RatFunc.algebraMap_X]

theorem u0_ne_zero : u0 q k ≠ 0 := by
  rw [u0]
  exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (P0_ne_zero q k)

theorem ord_placeOfPoint_u0 (a : k) :
    (placeOfPoint k a).ord (u0 q k) = rootMultiplicity a (P0 q k) :=
  ord_placeOfPoint_algebraMap a (P0_ne_zero q k)

theorem ord_placeInfty_u0 : (placeInfty k).ord (u0 q k) = -(q : ℤ) := by
  rw [u0, ord_placeInfty_algebraMap (P0_ne_zero q k), natDegree_P0]

theorem placeOfPoint_ne_placeInfty (a : k) : placeOfPoint k a ≠ placeInfty k := by
  intro h
  have h1 := ord_placeOfPoint_algebraMap (K := k) a (X_ne_zero (R := k))
  have h2 := ord_placeInfty_algebraMap (K := k) (X_ne_zero (R := k))
  rw [h, h2, natDegree_X] at h1
  have : (0 : ℤ) ≤ rootMultiplicity a (X : k[X]) := by positivity
  omega

noncomputable def S : Finset (Place k (RatFunc k)) :=
  insert (placeInfty k) ((P0 q k).roots.toFinset.image (placeOfPoint k))

theorem card_S : (S q k).card = q + 1 := by
  rw [S, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (placeOfPoint_injective k), card_roots_P0]
  simp only [Finset.mem_image, Multiset.mem_toFinset, not_exists, not_and]
  intro a _ h
  exact placeOfPoint_ne_placeInfty k a h

theorem placeInfty_mem_S : placeInfty k ∈ S q k := Finset.mem_insert_self _ _

theorem placeOfPoint_mem_S_iff (a : k) : placeOfPoint k a ∈ S q k ↔ (P0 q k).IsRoot a := by
  rw [S, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨b, hb, hba⟩)
    · exact absurd h (placeOfPoint_ne_placeInfty k a)
    · rw [placeOfPoint_injective k hba] at hb
      exact (mem_roots (P0_ne_zero q k)).mp (Multiset.mem_toFinset.mp hb)
  · intro h
    exact Or.inr ⟨a, Multiset.mem_toFinset.mpr ((mem_roots (P0_ne_zero q k)).mpr h), rfl⟩

end Count

section CountB

p2m_open "AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
open scoped Classical

set_option linter.unusedSectionVars false

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

scoped instance isCurveOver_inst : IsCurveOver k (drinfeldFunctionField q k) := isCurveOver_drinfeldFunctionField q k

theorem phi_u0 : phi q k (u0 q k) = wFF q k ^ (q + 1) := by
  rw [u0_eq, map_sub, map_pow, phi_X, wFF_pow]

theorem natCast_q_add_one_ne_zero : ((q + 1 : ℕ) : k) ≠ 0 := by
  haveI := charP_of_galoisField q k
  rw [Nat.cast_add, CharP.cast_eq_zero k q, zero_add, Nat.cast_one]
  exact one_ne_zero

theorem isCoprime_neg_q : IsCoprime (-(q : ℤ)) ((q + 1 : ℕ) : ℤ) :=
  ⟨1, 1, by push_cast; ring⟩

theorem ramificationIndex_eq_of_mem (w : Place k (drinfeldFunctionField q k))
    (hw : w.restrict (RatFunc k) ∈ S q k) : w.ramificationIndex (RatFunc k) = q + 1 := by
  refine Place.ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord (phi q k) (phi_isIntegral q k)
    (finiteAlong_phi q k) (separableAlong_phi q k) (q + 1) (finrankAlong_phi q k) (wFF q k) (u0 q k)
    (phi_u0 q k) w ?_
  change IsCoprime ((w.restrict (RatFunc k)).ord (u0 q k)) _
  rcases eq_placeOfPoint_or_eq_placeInfty k (w.restrict (RatFunc k)) with ⟨a, ha⟩ | h
  · rw [ha] at hw ⊢
    rw [ord_placeOfPoint_u0, rootMultiplicity_P0_of_isRoot q k ((placeOfPoint_mem_S_iff q k a).mp hw)]
    exact isCoprime_one_left
  · rw [h, ord_placeInfty_u0]
    exact isCoprime_neg_q q

theorem ramificationIndex_eq_of_not_mem (w : Place k (drinfeldFunctionField q k))
    (hw : w.restrict (RatFunc k) ∉ S q k) : w.ramificationIndex (RatFunc k) = 1 := by
  have hrat : (w.restrict (RatFunc k)).IsRational := Place.isRational_of_isAlgClosed _
  rcases eq_placeOfPoint_or_eq_placeInfty k (w.restrict (RatFunc k)) with ⟨a, ha⟩ | h
  · have hroot : ¬ (P0 q k).IsRoot a := fun hr => hw (ha ▸ (placeOfPoint_mem_S_iff q k a).mpr hr)
    have hord : (w.restrict (RatFunc k)).ord (u0 q k) = 0 := by
      rw [ha, ord_placeOfPoint_u0, rootMultiplicity_P0_of_not_isRoot q k hroot, Nat.cast_zero]
    have hmem : u0 q k ∈ (w.restrict (RatFunc k)).toValuationSubring ∧
        (u0 q k)⁻¹ ∈ (w.restrict (RatFunc k)).toValuationSubring := by
      constructor
      · exact (Place.mem_iff_ord_nonneg _ (u0_ne_zero q k)).mpr (by rw [hord])
      · exact (Place.mem_iff_ord_nonneg _ (inv_ne_zero (u0_ne_zero q k))).mpr
          (by rw [Place.ord_inv, hord, neg_zero])
    exact Place.ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem (phi q k) (phi_isIntegral q k) (q + 1)
      (natCast_q_add_one_ne_zero q k) (wFF q k) (closure_range_phi_eq_top q k) (u0 q k) (phi_u0 q k) w hrat hmem
  · exact absurd (h ▸ placeInfty_mem_S q k) hw

theorem natCast_ramificationIndex_ne_zero (w : Place k (drinfeldFunctionField q k)) :
    ((w.ramificationIndex (RatFunc k) : ℕ) : k) ≠ 0 := by
  by_cases hw : w.restrict (RatFunc k) ∈ S q k
  · rw [ramificationIndex_eq_of_mem q k w hw]; exact natCast_q_add_one_ne_zero q k
  · rw [ramificationIndex_eq_of_not_mem q k w hw, Nat.cast_one]; exact one_ne_zero

theorem card_fiber_eq_one {v : Place k (RatFunc k)} (hv : v ∈ S q k) :
    (v.fiber (drinfeldFunctionField q k)).card = 1 := by
  refine card_fiber_eq_one_of_forall_ramificationIndex_eq v (Place.isRational_of_isAlgClosed _)
    (fun w _ => Place.isRational_of_isAlgClosed _) (fun w hw => ?_)
  rw [finrank_ratFunc]
  exact ramificationIndex_eq_of_mem q k w ((Place.mem_fiber.mp hw).symm ▸ hv)

end CountB

section InftyCensus

p2m_open "AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
open scoped Classical

set_option linter.unusedSectionVars false

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

theorem ord_wFF_pow (v : Place k (drinfeldFunctionField q k)) :
    v.ord (wFF q k ^ (q + 1)) = (v.ramificationIndex (RatFunc k) : ℤ) * (v.restrict (RatFunc k)).ord (u0 q k) := by
  rw [← phi_u0, ← algebraMap_ratFunc_apply, Place.ord_restrict]

theorem ord_wFF (v : Place k (drinfeldFunctionField q k)) :
    (q + 1 : ℤ) * v.ord (wFF q k) = (v.ramificationIndex (RatFunc k) : ℤ) * (v.restrict (RatFunc k)).ord (u0 q k) := by
  rw [← ord_wFF_pow, ← Place.ord_zpow]
  norm_cast

theorem ord_wFF_eq_zero_of_not_mem (v : Place k (drinfeldFunctionField q k)) (hv : v.restrict (RatFunc k) ∉ S q k) :
    v.ord (wFF q k) = 0 := by
  have h := ord_wFF q k v
  rcases eq_placeOfPoint_or_eq_placeInfty k (v.restrict (RatFunc k)) with ⟨a, ha⟩ | hinf
  · have hroot : ¬ (P0 q k).IsRoot a := fun hr => hv (ha ▸ (placeOfPoint_mem_S_iff q k a).mpr hr)
    rw [ha, ord_placeOfPoint_u0, rootMultiplicity_P0_of_not_isRoot q k hroot, Nat.cast_zero, mul_zero] at h
    have : (0 : ℤ) < q + 1 := by positivity
    exact (mul_eq_zero.mp h).resolve_left this.ne'
  · exact absurd (hinf ▸ placeInfty_mem_S q k) hv

theorem ord_wFF_eq_one_of_eq_placeOfPoint (v : Place k (drinfeldFunctionField q k)) {a : k}
    (ha : v.restrict (RatFunc k) = placeOfPoint k a) (hroot : (P0 q k).IsRoot a) :
    v.ord (wFF q k) = 1 := by
  have h := ord_wFF q k v
  have hmem : v.restrict (RatFunc k) ∈ S q k := ha ▸ (placeOfPoint_mem_S_iff q k a).mpr hroot
  rw [ramificationIndex_eq_of_mem q k v hmem, ha, ord_placeOfPoint_u0, rootMultiplicity_P0_of_isRoot q k hroot] at h
  push_cast at h
  have : (0 : ℤ) < q + 1 := by positivity
  nlinarith [h]

theorem ord_wFF_eq_of_eq_placeInfty (v : Place k (drinfeldFunctionField q k))
    (hinf : v.restrict (RatFunc k) = placeInfty k) : v.ord (wFF q k) = -(q : ℤ) := by
  have h := ord_wFF q k v
  rw [ramificationIndex_eq_of_mem q k v (hinf ▸ placeInfty_mem_S q k), hinf, ord_placeInfty_u0] at h
  push_cast at h
  have : (0 : ℤ) < q + 1 := by positivity
  nlinarith [h]

#print "INF-core-ok"
end InftyCensus

section InftyCensus2
p2m_open "AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
open scoped Classical

set_option linter.unusedSectionVars false

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

theorem isRoot_P0_iff (a : k) : (P0 q k).IsRoot a ↔ a ^ q = a := by
  rw [P0, IsRoot.def, eval_sub, eval_X, eval_pow, eval_X, sub_eq_zero, eq_comm]

theorem ord_uFF (v : Place k (drinfeldFunctionField q k)) :
    v.ord (uFF q k) = (v.ramificationIndex (RatFunc k) : ℤ) * (v.restrict (RatFunc k)).ord RatFunc.X := by
  rw [← phi_X, ← algebraMap_ratFunc_apply, Place.ord_restrict]

theorem ord_uFF_sub (v : Place k (drinfeldFunctionField q k)) (a : k) :
    v.ord (uFF q k - algebraMap k (drinfeldFunctionField q k) a) =
      (v.ramificationIndex (RatFunc k) : ℤ) *
        (v.restrict (RatFunc k)).ord (algebraMap k[X] (RatFunc k) (X - C a)) := by
  have : uFF q k - algebraMap k (drinfeldFunctionField q k) a =
      algebraMap (RatFunc k) (drinfeldFunctionField q k) (algebraMap k[X] (RatFunc k) (X - C a)) := by
    simp only [algebraMap_ratFunc_apply, map_sub, RatFunc.algebraMap_X, phi_X, RatFunc.algebraMap_C, phi_C]
  rw [this, Place.ord_restrict]

theorem ramificationIndex_pos' (v : Place k (drinfeldFunctionField q k)) : 0 < (v.ramificationIndex (RatFunc k) : ℤ) := by
  exact_mod_cast v.ramificationIndex_pos (F := RatFunc k)

theorem ord_uFF_sub_pos_iff (v : Place k (drinfeldFunctionField q k)) (a : k) :
    0 < v.ord (uFF q k - algebraMap k (drinfeldFunctionField q k) a) ↔ v.restrict (RatFunc k) = placeOfPoint k a := by
  rw [ord_uFF_sub]
  have he := ramificationIndex_pos' q k v
  have he' := v.ramificationIndex_pos (F := RatFunc k)
  rcases eq_placeOfPoint_or_eq_placeInfty k (v.restrict (RatFunc k)) with ⟨c, hc⟩ | hinf
  · rw [hc, ord_placeOfPoint_algebraMap c (X_sub_C_ne_zero a), rootMultiplicity_X_sub_C]
    constructor
    · intro h
      by_cases hca : c = a
      · rw [hca]
      · simp [hca] at h
    · intro h
      rw [placeOfPoint_injective k h]
      simp [he']
  · rw [hinf, ord_placeInfty_algebraMap (X_sub_C_ne_zero a), natDegree_X_sub_C]
    constructor
    · intro h; nlinarith
    · intro h; exact absurd h.symm (placeOfPoint_ne_placeInfty k a)

theorem uFF_not_mem_iff (v : Place k (drinfeldFunctionField q k)) :
    uFF q k ∉ v.toValuationSubring ↔ v.restrict (RatFunc k) = placeInfty k := by
  rw [Place.mem_iff_ord_nonneg _ (uFF_ne_zero q k), ord_uFF, not_le]
  have he := ramificationIndex_pos' q k v
  have he' := v.ramificationIndex_pos (F := RatFunc k)
  rcases eq_placeOfPoint_or_eq_placeInfty k (v.restrict (RatFunc k)) with ⟨c, hc⟩ | hinf
  · rw [hc, show (RatFunc.X : RatFunc k) = algebraMap k[X] (RatFunc k) X from RatFunc.algebraMap_X.symm,
      ord_placeOfPoint_algebraMap c X_ne_zero]
    constructor
    · intro h
      have : (0 : ℤ) ≤ rootMultiplicity c (X : k[X]) := by positivity
      nlinarith
    · intro h; exact absurd h (placeOfPoint_ne_placeInfty k c)
  · rw [hinf, show (RatFunc.X : RatFunc k) = algebraMap k[X] (RatFunc k) X from RatFunc.algebraMap_X.symm,
      ord_placeInfty_algebraMap X_ne_zero, natDegree_X]
    simp [he']

theorem not_mem_or_not_mem_iff_mem_S (v : Place k (drinfeldFunctionField q k)) :
    (xF q k ∉ v.toValuationSubring ∨ yF q k ∉ v.toValuationSubring) ↔ v.restrict (RatFunc k) ∈ S q k := by
  constructor
  · intro h
    by_contra hv
    have hw0 := ord_wFF_eq_zero_of_not_mem q k v hv
    have hy : yF q k ∈ v.toValuationSubring := by
      rw [yF_eq, Place.mem_iff_ord_nonneg _ (inv_ne_zero (wFF_ne_zero q k)), Place.ord_inv, hw0, neg_zero]
    have hne : v.restrict (RatFunc k) ≠ placeInfty k := fun h' => hv (h' ▸ placeInfty_mem_S q k)
    have hu : uFF q k ∈ v.toValuationSubring := by
      by_contra hu
      exact hne ((uFF_not_mem_iff q k v).mp hu)
    have hx : xF q k ∈ v.toValuationSubring := by
      rw [xF_eq, div_eq_mul_inv, ← yF_eq]
      exact mul_mem hu hy
    rcases h with h | h
    · exact h hx
    · exact h hy
  · intro hv
    rcases eq_placeOfPoint_or_eq_placeInfty k (v.restrict (RatFunc k)) with ⟨a, ha⟩ | hinf
    · right
      have hroot : (P0 q k).IsRoot a := (placeOfPoint_mem_S_iff q k a).mp (ha ▸ hv)
      have h1 := ord_wFF_eq_one_of_eq_placeOfPoint q k v ha hroot
      rw [yF_eq, Place.mem_iff_ord_nonneg _ (inv_ne_zero (wFF_ne_zero q k)), Place.ord_inv, h1]
      norm_num
    · left
      have hw := ord_wFF_eq_of_eq_placeInfty q k v hinf
      have hu : v.ord (uFF q k) = -(q + 1 : ℤ) := by
        rw [ord_uFF, ramificationIndex_eq_of_mem q k v hv, hinf,
          show (RatFunc.X : RatFunc k) = algebraMap k[X] (RatFunc k) X from RatFunc.algebraMap_X.symm,
          ord_placeInfty_algebraMap X_ne_zero, natDegree_X]
        push_cast
        ring
      rw [xF_eq, Place.mem_iff_ord_nonneg _ (div_ne_zero (uFF_ne_zero q k) (wFF_ne_zero q k)), div_eq_mul_inv,
        Place.ord_mul _ (uFF_ne_zero q k) (inv_ne_zero (wFF_ne_zero q k)), Place.ord_inv, hu, hw]
      push_cast
      omega

theorem natCard_setOf_not_mem_or_not_mem :
    Nat.card {v : Place k (drinfeldFunctionField q k) //
      xF q k ∉ v.toValuationSubring ∨ yF q k ∉ v.toValuationSubring} = q + 1 := by
  have hset : ∀ v : Place k (drinfeldFunctionField q k),
      (xF q k ∉ v.toValuationSubring ∨ yF q k ∉ v.toValuationSubring) ↔
        v ∈ (S q k).biUnion (fun s => s.fiber (drinfeldFunctionField q k)) := by
    intro v
    rw [not_mem_or_not_mem_iff_mem_S, Finset.mem_biUnion]
    constructor
    · intro h; exact ⟨_, h, Place.restrict_mem_fiber v⟩
    · rintro ⟨s, hs, hv⟩; rwa [Place.mem_fiber.mp hv]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_eq_finsetCard, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun s hs => card_fiber_eq_one q k hs), Finset.sum_const, card_S, smul_eq_mul, mul_one]
  · intro s _ t _ hst
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    exact hst ((Place.mem_fiber.mp hw).symm.trans (Place.mem_fiber.mp hw'))

theorem existsUnique_ord_uFF_sub_pos {a : k} (ha : a ^ q = a) :
    ∃! v : Place k (drinfeldFunctionField q k), 0 < v.ord (uFF q k - algebraMap k (drinfeldFunctionField q k) a) := by
  have hmem : placeOfPoint k a ∈ S q k := (placeOfPoint_mem_S_iff q k a).mpr ((isRoot_P0_iff q k a).mpr ha)
  have hc := card_fiber_eq_one q k hmem
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  refine ⟨v, (ord_uFF_sub_pos_iff q k v a).mpr (Place.mem_fiber.mp (hv ▸ Finset.mem_singleton_self v)), ?_⟩
  intro w hw
  have : w ∈ (placeOfPoint k a).fiber (drinfeldFunctionField q k) := Place.mem_fiber.mpr ((ord_uFF_sub_pos_iff q k w a).mp hw)
  rw [hv] at this
  exact Finset.mem_singleton.mp this

theorem existsUnique_uFF_not_mem :
    ∃! v : Place k (drinfeldFunctionField q k), uFF q k ∉ v.toValuationSubring := by
  have hc := card_fiber_eq_one q k (placeInfty_mem_S q k)
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  refine ⟨v, (uFF_not_mem_iff q k v).mpr (Place.mem_fiber.mp (hv ▸ Finset.mem_singleton_self v)), ?_⟩
  intro w hw
  have : w ∈ (placeInfty k).fiber (drinfeldFunctionField q k) := Place.mem_fiber.mpr ((uFF_not_mem_iff q k w).mp hw)
  rw [hv] at this
  exact Finset.mem_singleton.mp this

theorem not_mem_or_not_mem_iff_direction (v : Place k (drinfeldFunctionField q k)) :
    (xF q k ∉ v.toValuationSubring ∨ yF q k ∉ v.toValuationSubring) ↔
      (uFF q k ∉ v.toValuationSubring ∨
        ∃ a : k, a ^ q = a ∧ 0 < v.ord (uFF q k - algebraMap k (drinfeldFunctionField q k) a)) := by
  rw [not_mem_or_not_mem_iff_mem_S, uFF_not_mem_iff]
  constructor
  · intro hv
    rcases eq_placeOfPoint_or_eq_placeInfty k (v.restrict (RatFunc k)) with ⟨a, ha⟩ | hinf
    · right
      exact ⟨a, (isRoot_P0_iff q k a).mp ((placeOfPoint_mem_S_iff q k a).mp (ha ▸ hv)),
        (ord_uFF_sub_pos_iff q k v a).mpr ha⟩
    · left; exact hinf
  · rintro (hinf | ⟨a, ha, hpos⟩)
    · rw [hinf]; exact placeInfty_mem_S q k
    · rw [(ord_uFF_sub_pos_iff q k v a).mp hpos]
      exact (placeOfPoint_mem_S_iff q k a).mpr ((isRoot_P0_iff q k a).mpr ha)

#print "CENSUS-ok"
end InftyCensus2

section InftyCensus3
p2m_open "AlgebraicCurve AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
open scoped Classical
set_option linter.unusedSectionVars false
variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

theorem eq_of_ord_uFF_sub_pos {a : k} (ha : a ^ q = a) {v w : Place k (drinfeldFunctionField q k)}
    (hv : 0 < v.ord (uFF q k - algebraMap k (drinfeldFunctionField q k) a))
    (hw : 0 < w.ord (uFF q k - algebraMap k (drinfeldFunctionField q k) a)) : v = w :=
  (existsUnique_ord_uFF_sub_pos q k ha).unique hv hw

theorem eq_of_uFF_not_mem {v w : Place k (drinfeldFunctionField q k)}
    (hv : uFF q k ∉ v.toValuationSubring) (hw : uFF q k ∉ w.toValuationSubring) : v = w :=
  (existsUnique_uFF_not_mem q k).unique hv hw

end InftyCensus3

section AffineCensus

open AlgebraicCurve Polynomial MvPolynomial
open scoped Classical
set_option linter.unusedSectionVars false

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

noncomputable def fPoly : MvPolynomial (Fin 2) k := drinfeldPoly q k - 1

theorem aeval_xF_yF (g : MvPolynomial (Fin 2) k) :
    MvPolynomial.aeval ![xF q k, yF q k] g = algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k g) := by
  have h : (MvPolynomial.aeval ![xF q k, yF q k] : MvPolynomial (Fin 2) k →ₐ[k] drinfeldFunctionField q k) =
      (IsScalarTower.toAlgHom k (CoordRing q k) (drinfeldFunctionField q k)).comp (mk q k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [xF, x]
    · simp [yF, y]
  exact AlgHom.congr_fun h g

theorem aeval_fPoly : MvPolynomial.aeval ![xF q k, yF q k] (fPoly q k) = 0 := by
  rw [aeval_xF_yF, fPoly, map_sub, map_one, mk_drinfeldPoly, sub_self, map_zero]

theorem ker_aeval (g : MvPolynomial (Fin 2) k) (hg : MvPolynomial.aeval ![xF q k, yF q k] g = 0) :
    g ∈ Ideal.span {fPoly q k} := by
  rw [aeval_xF_yF, map_eq_zero_iff _ (IsFractionRing.injective (CoordRing q k) (drinfeldFunctionField q k))] at hg
  have : (Ideal.Quotient.mk (drinfeldIdeal q k) g) = 0 := hg
  rwa [Ideal.Quotient.eq_zero_iff_mem] at this

theorem closure_xF_yF_eq_top :
    Subfield.closure (Set.range (algebraMap k (drinfeldFunctionField q k)) ∪ {xF q k, yF q k}) = ⊤ := by

  set L := Subfield.closure (Set.range (algebraMap k (drinfeldFunctionField q k)) ∪ {xF q k, yF q k})
  have hC : ∀ c : CoordRing q k, algebraMap (CoordRing q k) (drinfeldFunctionField q k) c ∈ L := by
    intro c
    obtain ⟨g, rfl⟩ := mk_surjective q k c
    rw [← aeval_xF_yF]
    induction g using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.aeval_C]
      exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
    | add p p' hp hp' => rw [map_add]; exact add_mem hp hp'
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ?_))
      fin_cases i <;> simp
  rw [eq_top_iff]
  intro z _
  obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := CoordRing q k) z
  exact div_mem (hC c) (hC d)

theorem eval_fPoly (a b : k) : MvPolynomial.eval ![a, b] (fPoly q k) = a * b ^ q - a ^ q * b - 1 := by
  simp [fPoly, drinfeldPoly]

theorem eval_pderiv_fPoly (a b : k) : MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 1 (fPoly q k)) = -a ^ q := by
  haveI := charP_of_galoisField q k
  simp [fPoly, drinfeldPoly, MvPolynomial.pderiv_X, Pi.single_apply, CharP.cast_eq_zero k q]

theorem ne_zero_of_point {a b : k} (hab : a * b ^ q - a ^ q * b = 1) : a ≠ 0 := by
  rintro rfl
  have h1 : 1 < q := one_lt_q q
  simp [zero_pow (by omega : q ≠ 0)] at hab

theorem existsUnique_place_of_point {a b : k} (hab : a * b ^ q - a ^ q * b = 1) :
    ∃! v : Place k (drinfeldFunctionField q k),
      xF q k - algebraMap k (drinfeldFunctionField q k) a ∈ v.toValuationSubring.nonunits ∧
        yF q k - algebraMap k (drinfeldFunctionField q k) b ∈ v.toValuationSubring.nonunits := by
  refine Place.existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero (xF q k) (yF q k) (fPoly q k)
    (aeval_fPoly q k) (ker_aeval q k) (closure_xF_yF_eq_top q k) a b ?_ ?_
  · rw [eval_fPoly, hab, sub_self]
  · rw [eval_pderiv_fPoly]
    exact neg_ne_zero.mpr (pow_ne_zero _ (ne_zero_of_point q k hab))

#print "AFF-1-ok"
end AffineCensus

section AffineCensus2
open AlgebraicCurve Polynomial
open scoped Classical
set_option linter.unusedSectionVars false

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

omit hq [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (CoordRing q k)] in

theorem mem_nonunits_iff_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf0 : f ≠ 0) :
    f ∈ v.toValuationSubring.nonunits ↔ 0 < v.ord f := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hf, hmax⟩
    have h1 : 0 ≤ v.ord f := (Place.mem_iff_ord_nonneg v hf0).mp hf
    have h2 : v.ord f ≠ 0 := by
      rw [Ne, v.ord_eq_zero_iff_adicValuation_eq_one hf0]
      exact ((v.mem_maximalIdeal_iff_adicValuation_lt_one ⟨f, hf⟩).mp hmax).ne
    omega
  · intro h
    have hf : f ∈ v.toValuationSubring := (Place.mem_iff_ord_nonneg v hf0).mpr h.le
    refine ⟨hf, (v.mem_maximalIdeal_iff_adicValuation_lt_one ⟨f, hf⟩).mpr ?_⟩
    exact lt_of_le_of_ne (v.mem_iff_adicValuation_le_one.mp hf)
      (fun h1 => h.ne' ((v.ord_eq_zero_iff_adicValuation_eq_one hf0).mpr h1))

theorem xF_ne_algebraMap (a : k) : xF q k ≠ algebraMap k (drinfeldFunctionField q k) a := by
  intro h

  obtain ⟨v, hv, -⟩ := existsUnique_uFF_not_mem q k
  have hinf := (uFF_not_mem_iff q k v).mp hv
  have hx : xF q k ∉ v.toValuationSubring := by
    have := (not_mem_or_not_mem_iff_mem_S q k v).mpr (hinf ▸ placeInfty_mem_S q k)

    rcases this with hx | hy
    · exact hx
    · exfalso
      apply hy
      rw [yF_eq, Place.mem_iff_ord_nonneg _ (inv_ne_zero (wFF_ne_zero q k)), Place.ord_inv,
        ord_wFF_eq_of_eq_placeInfty q k v hinf]
      simp
  exact hx (h ▸ v.algebraMap_mem' a)

theorem yF_ne_algebraMap (b : k) : yF q k ≠ algebraMap k (drinfeldFunctionField q k) b := by
  intro h
  obtain ⟨a, ha⟩ : ∃ a : k, a ^ q = a := ⟨0, by rw [zero_pow (one_lt_q q).ne_bot]⟩
  obtain ⟨v, hv, -⟩ := existsUnique_ord_uFF_sub_pos q k ha
  have hpt := (ord_uFF_sub_pos_iff q k v a).mp hv
  have hy : yF q k ∉ v.toValuationSubring := by
    rw [yF_eq, Place.mem_iff_ord_nonneg _ (inv_ne_zero (wFF_ne_zero q k)), Place.ord_inv,
      ord_wFF_eq_one_of_eq_placeOfPoint q k v hpt ((isRoot_P0_iff q k a).mpr ha)]
    norm_num
  exact hy (h ▸ v.algebraMap_mem' b)

theorem exists_point_of_mem_of_mem (v : Place k (drinfeldFunctionField q k))
    (hx : xF q k ∈ v.toValuationSubring) (hy : yF q k ∈ v.toValuationSubring) :
    ∃ a b : k, a * b ^ q - a ^ q * b = 1 ∧
      xF q k - algebraMap k (drinfeldFunctionField q k) a ∈ v.toValuationSubring.nonunits ∧
        yF q k - algebraMap k (drinfeldFunctionField q k) b ∈ v.toValuationSubring.nonunits := by
  have hv : v.IsRational := Place.isRational_of_isAlgClosed v
  refine ⟨v.evalAt (xF q k), v.evalAt (yF q k), ?_, ?_, ?_⟩
  ·
    apply (algebraMap k v.ResidueField).injective
    have hxr := v.algebraMap_evalAt hv hx
    have hyr := v.algebraMap_evalAt hv hy
    simp only [map_sub, map_mul, map_pow, map_one, hxr, hyr]
    have hrel : (⟨xF q k, hx⟩ * ⟨yF q k, hy⟩ ^ q - ⟨xF q k, hx⟩ ^ q * ⟨yF q k, hy⟩ : v.toValuationSubring) = 1 := by
      apply Subtype.ext
      simp [relF q k]
    have h := congrArg (IsLocalRing.residue v.toValuationSubring) hrel
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, RingHom.map_one] at h
    exact h
  · rw [mem_nonunits_iff_ord_pos _ (sub_ne_zero.mpr (xF_ne_algebraMap q k _))]
    exact (Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v hv _ _ (xF_ne_algebraMap q k _)).mp ⟨hx, rfl⟩
  · rw [mem_nonunits_iff_ord_pos _ (sub_ne_zero.mpr (yF_ne_algebraMap q k _))]
    exact (Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v hv _ _ (yF_ne_algebraMap q k _)).mp ⟨hy, rfl⟩

#print "AFF-2-ok"
end AffineCensus2

end GenusAux
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux"
end DrinfeldCurve
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

noncomputable section

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_mu drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext mk_drinfeldPoly x y relation muAction muAction_x muAction_y one_mem_hSubgroup_of_mem isCurveOver_drinfeldFunctionField finite_and_ncard_setOf_twistedFrobenius_affineFixed"
p2m_open "DrinfeldCurve"

namespace CNTAux

open AlgebraicCurve IsLocalRing

section Nonunits

variable {F : Type*} [Field F]

theorem mem_nonunits_iff' (A : ValuationSubring F) (g : F) : g ∈ A.nonunits ↔ g = 0 ∨ g⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le]
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [one_lt_inv₀ ((map_ne_zero _).mpr hg |>.bot_lt)]
    simp [hg]

theorem mem_nonunits_comap_iff {F' : Type*} [Field F'] (A : ValuationSubring F') (φ : F →+* F') (g : F) :
    g ∈ (A.comap φ).nonunits ↔ φ g ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

variable {K : Type*} [Field K] [Algebra K F]

open scoped Pointwise in

theorem mem_nonunits_smul_iff (σ : F ≃ₐ[K] F) (A : ValuationSubring F) (g : F) :
    g ∈ (σ • A).nonunits ↔ σ.symm g ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    map_inv₀, EmbeddingLike.map_eq_zero_iff]
  rfl

theorem mul_mem_nonunits (A : ValuationSubring F) {a g : F} (ha : a ∈ A) (hg : g ∈ A.nonunits) : a * g ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hg ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at ha
  calc A.valuation (a * g) = A.valuation a * A.valuation g := map_mul _ _ _
    _ ≤ 1 * A.valuation g := mul_le_mul_left ha _
    _ = A.valuation g := one_mul _
    _ < 1 := hg

theorem pow_mem_nonunits (A : ValuationSubring F) {g : F} (hg : g ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) : g ^ n ∈ A.nonunits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  have hgA : g ∈ A := A.nonunits_le hg
  exact mul_mem_nonunits A (pow_mem hgA m) hg

theorem sub_mem_nonunits (A : ValuationSubring F) {g g' : F} (hg : g ∈ A.nonunits) (hg' : g' ∈ A.nonunits) : g - g' ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hg hg' ⊢
  exact lt_of_le_of_lt (A.valuation.map_sub g g') (max_lt hg hg')

end Nonunits
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

section Values

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (v : Place k F)

def HasVal (f : F) (c : k) : Prop := f - algebraMap k F c ∈ v.toValuationSubring.nonunits

variable {v}

theorem HasVal.mem {f : F} {c : k} (h : HasVal v f c) : f ∈ v.toValuationSubring := by
  have := add_mem (v.toValuationSubring.nonunits_le h) (v.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

theorem HasVal.unique {f : F} {c c' : k} (h : HasVal v f c) (h' : HasVal v f c') : c = c' := by
  by_contra hne
  have hd : algebraMap k F (c' - c) ∈ v.toValuationSubring.nonunits := by
    have := sub_mem_nonunits _ h h'
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  rw [mem_nonunits_iff', map_eq_zero, sub_eq_zero, ← map_inv₀] at hd
  rcases hd with hd | hd
  · exact hne hd.symm
  · exact hd (v.algebraMap_mem' _)

theorem hasVal_iff_residue {f : F} (hf : f ∈ v.toValuationSubring) (c : k) :
    HasVal v f c ↔ residue v.toValuationSubring ⟨f, hf⟩ = algebraMap k v.ResidueField c := by
  rw [HasVal]
  have hmem : f - algebraMap k F c ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' c)
  rw [show f - algebraMap k F c = ((⟨f - algebraMap k F c, hmem⟩ : v.toValuationSubring) : F) from rfl,
    ValuationSubring.coe_mem_nonunits_iff, ← residue_eq_zero_iff]
  have : (⟨f - algebraMap k F c, hmem⟩ : v.toValuationSubring) = ⟨f, hf⟩ - algebraMap k v.toValuationSubring c := by
    apply Subtype.ext; simp [Place.coe_algebraMap]
  rw [this, map_sub, sub_eq_zero, IsScalarTower.algebraMap_apply k v.toValuationSubring v.ResidueField c,
    IsLocalRing.ResidueField.algebraMap_eq]

theorem exists_hasVal (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) : ∃ c : k, HasVal v f c :=
  ⟨v.evalAt f, (hasVal_iff_residue hf _).mpr (v.algebraMap_evalAt hv hf).symm⟩

theorem hasVal_algebraMap (c : k) : HasVal v (algebraMap k F c) c := by
  rw [HasVal, sub_self]
  exact (mem_nonunits_iff' _ _).mpr (Or.inl rfl)

theorem HasVal.mul {f g : F} {c d : k} (hf : HasVal v f c) (hg : HasVal v g d) : HasVal v (f * g) (c * d) := by
  have hfm := hf.mem
  have hgm := hg.mem
  rw [hasVal_iff_residue hfm] at hf
  rw [hasVal_iff_residue hgm] at hg
  rw [hasVal_iff_residue (mul_mem hfm hgm)]
  have : (⟨f * g, mul_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ * ⟨g, hgm⟩ := rfl
  rw [this, map_mul, hf, hg, ← map_mul]

theorem HasVal.pow {f : F} {c : k} (hf : HasVal v f c) (n : ℕ) : HasVal v (f ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← (algebraMap k F).map_one]; exact hasVal_algebraMap 1
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hf

theorem HasVal.sub {f g : F} {c d : k} (hf : HasVal v f c) (hg : HasVal v g d) : HasVal v (f - g) (c - d) := by
  have := sub_mem_nonunits _ hf hg
  rw [HasVal, map_sub]
  convert this using 1
  ring

theorem HasVal.const_mul (e : k) {f : F} {c : k} (hf : HasVal v f c) : HasVal v (algebraMap k F e * f) (e * c) :=
  (hasVal_algebraMap e).mul hf

theorem HasVal.eq_one_of_eq_one {f : F} {c : k} (hf : HasVal v f c) (h1 : f = 1) : c = 1 := by
  apply hf.unique
  rw [h1, ← (algebraMap k F).map_one]
  exact hasVal_algebraMap 1

end Values
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

section Transport

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem hasVal_restrictAlong_iff (φ : F →ₐ[k] F) (hφ : φ.toRingHom.IsIntegral) (w : Place k F) (f : F) (c : k) :
    HasVal (w.restrictAlong φ hφ) f c ↔ HasVal w (φ f) c := by
  rw [HasVal, HasVal]
  have : (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom := rfl
  rw [this, mem_nonunits_comap_iff]
  simp

theorem hasVal_smul_iff (σ : F ≃ₐ[k] F) (w : Place k F) (f : F) (c : k) :
    HasVal (σ • w) f c ↔ HasVal w (σ.symm f) c := by
  rw [HasVal, HasVal, Place.smul_toValuationSubring, mem_nonunits_smul_iff, map_sub, AlgEquiv.commutes]

end Transport
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

section Drinfeld

variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

theorem charP_k : CharP k q := charP_of_injective_algebraMap' (GaloisField q 2) q

theorem charP_F : CharP (drinfeldFunctionField q k) q := by
  haveI := charP_k q k
  exact charP_of_injective_algebraMap (algebraMap k (drinfeldFunctionField q k)).injective q

private abbrev _root_.DrinfeldCurve.CNTAux.xF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)
p2m_export "DrinfeldCurve.CNTAux" "xF"
private abbrev _root_.DrinfeldCurve.CNTAux.yF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)

p2m_export "DrinfeldCurve.CNTAux" "yF"
theorem relF : xF q k * yF q k ^ q - xF q k ^ q * yF q k = 1 := by
  have h := congrArg (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) (relation q k)
  simp only [map_sub, map_mul, map_pow, map_one] at h
  exact h

variable (η : rootsOfUnity (q + 1) (GaloisField q 2))

abbrev ση : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k :=
  hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q η⟩

abbrev ηk : k := algebraMap (GaloisField q 2) k ((η : (GaloisField q 2)ˣ) : GaloisField q 2)

theorem ηk_ne_zero : ηk q k η ≠ 0 := by
  rw [ηk, map_ne_zero]; exact Units.ne_zero _

theorem ση_eq : ση q k η = IsFractionRing.algEquivOfAlgEquiv (muAction q k η) := hFunctionFieldAction_mu q k η

theorem ση_xF : ση q k η (xF q k) = algebraMap k _ (ηk q k η) * xF q k := by
  rw [ση_eq, xF, IsFractionRing.algEquivOfAlgEquiv_algebraMap, muAction_x, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem ση_yF : ση q k η (yF q k) = algebraMap k _ (ηk q k η) * yF q k := by
  rw [ση_eq, yF, IsFractionRing.algEquivOfAlgEquiv_algebraMap, muAction_y, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem ση_symm_xF : (ση q k η).symm (xF q k) = algebraMap k _ (ηk q k η)⁻¹ * xF q k := by
  rw [AlgEquiv.symm_apply_eq, map_mul, AlgEquiv.commutes, ση_xF, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (ηk_ne_zero q k η),
    map_one, one_mul]

theorem ση_symm_yF : (ση q k η).symm (yF q k) = algebraMap k _ (ηk q k η)⁻¹ * yF q k := by
  rw [AlgEquiv.symm_apply_eq, map_mul, AlgEquiv.commutes, ση_yF, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (ηk_ne_zero q k η),
    map_one, one_mul]

variable (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)

theorem value_transport {w : Place k (drinfeldFunctionField q k)} (hrel : w.restrictAlong φ hφi = ση q k η • w)
    {f : drinfeldFunctionField q k} {c : k} (hf : HasVal w f c) (hφf : φ f = f ^ q ^ 2)
    (hσf : (ση q k η).symm f = algebraMap k _ (ηk q k η)⁻¹ * f) : ηk q k η * c ^ q ^ 2 = c := by
  haveI := charP_k q k
  haveI := charP_F q k

  have h1 : HasVal (w.restrictAlong φ hφi) f (c ^ q ^ 2) := by
    rw [hasVal_restrictAlong_iff, hφf]
    exact hf.pow _

  have h2 : HasVal (w.restrictAlong φ hφi) f ((ηk q k η)⁻¹ * c) := by
    rw [hrel, hasVal_smul_iff, hσf]
    exact hf.const_mul _
  have h := h1.unique h2
  rw [h, ← mul_assoc, mul_inv_cancel₀ (ηk_ne_zero q k η), one_mul]

theorem values_mem_affineFixed (hφx : φ (xF q k) = xF q k ^ q ^ 2) (hφy : φ (yF q k) = yF q k ^ q ^ 2)
    {w : Place k (drinfeldFunctionField q k)} (hw : w.IsRational)
    (hx : xF q k ∈ w.toValuationSubring) (hy : yF q k ∈ w.toValuationSubring)
    (hrel : w.restrictAlong φ hφi = ση q k η • w) :
    ∃ a b : k, HasVal w (xF q k) a ∧ HasVal w (yF q k) b ∧
      a * b ^ q - a ^ q * b = 1 ∧ ηk q k η * a ^ q ^ 2 = a ∧ ηk q k η * b ^ q ^ 2 = b := by
  obtain ⟨a, ha⟩ := exists_hasVal hw hx
  obtain ⟨b, hb⟩ := exists_hasVal hw hy
  refine ⟨a, b, ha, hb, ?_, ?_, ?_⟩
  · exact ((ha.mul (hb.pow q)).sub ((ha.pow q).mul hb)).eq_one_of_eq_one (relF q k)
  · exact value_transport q k η φ hφi hrel ha hφx (ση_symm_xF q k η)
  · exact value_transport q k η φ hφi hrel hb hφy (ση_symm_yF q k η)

end Drinfeld
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

end CNTAux
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

end DrinfeldCurve
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

end
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_mu drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext mk_drinfeldPoly x y relation muAction muAction_x muAction_y one_mem_hSubgroup_of_mem isCurveOver_drinfeldFunctionField finite_and_ncard_setOf_twistedFrobenius_affineFixed"
p2m_open "DrinfeldCurve"
namespace MaxAux

open AlgebraicCurve DrinfeldCurve.CNTAux
open scoped Classical Pointwise

set_option linter.unusedSectionVars false

section
variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]

theorem xF_eq : GenusAux.xF q k = CNTAux.xF q k := rfl
theorem yF_eq : GenusAux.yF q k = CNTAux.yF q k := rfl
theorem uFF_eq : GenusAux.uFF q k = CNTAux.xF q k / CNTAux.yF q k := rfl

theorem hasVal_evalAt {w : Place k (drinfeldFunctionField q k)} (hw : w.IsRational) {f : drinfeldFunctionField q k}
    (hf : f ∈ w.toValuationSubring) : HasVal w f (w.evalAt f) :=
  (hasVal_iff_residue hf _).mpr (w.algebraMap_evalAt hw hf).symm

theorem isRational (w : Place k (drinfeldFunctionField q k)) : w.IsRational := Place.isRational_of_isAlgClosed w

theorem rel_pow {a b : k} (hab : a * b ^ q - a ^ q * b = 1) (n : ℕ) :
    a ^ q ^ n * (b ^ q ^ n) ^ q - (a ^ q ^ n) ^ q * b ^ q ^ n = 1 := by
  haveI := charP_k q k
  have h := congrArg (fun t : k => t ^ q ^ n) hab
  beta_reduce at h
  rw [one_pow, sub_pow_char_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at h
  rw [← pow_mul, ← pow_mul, mul_comm (q ^ n) q]
  exact h

variable (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
  (hφx : φ (CNTAux.xF q k) = CNTAux.xF q k ^ q ^ 2) (hφy : φ (CNTAux.yF q k) = CNTAux.yF q k ^ q ^ 2)
  (ζ : rootsOfUnity (q + 1) (GaloisField q 2))

def Rel (w : Place k (drinfeldFunctionField q k)) : Prop := w.restrictAlong φ hφi = ση q k ζ • w

def Aff (w : Place k (drinfeldFunctionField q k)) : Prop :=
  CNTAux.xF q k ∈ w.toValuationSubring ∧ CNTAux.yF q k ∈ w.toValuationSubring

def S : Set (k × k) :=
  {p : k × k | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧ ηk q k ζ * p.1 ^ q ^ 2 = p.1 ∧ ηk q k ζ * p.2 ^ q ^ 2 = p.2}

include hφx hφy in

theorem rel_of_hasVal {w : Place k (drinfeldFunctionField q k)} {a b : k} (hp : (a, b) ∈ S q k ζ)
    (ha : HasVal w (CNTAux.xF q k) a) (hb : HasVal w (CNTAux.yF q k) b) : Rel q k φ hφi ζ w := by
  obtain ⟨hab, hfa, hfb⟩ := hp

  have hcurve : a ^ q ^ 2 * (b ^ q ^ 2) ^ q - (a ^ q ^ 2) ^ q * b ^ q ^ 2 = 1 := rel_pow q k hab 2
  obtain ⟨v, hv, huniq⟩ := GenusAux.existsUnique_place_of_point q k hcurve
  have h1 : w.restrictAlong φ hφi = v := by
    apply huniq
    constructor
    · have : HasVal (w.restrictAlong φ hφi) (CNTAux.xF q k) (a ^ q ^ 2) := by
        rw [hasVal_restrictAlong_iff, hφx]; exact ha.pow _
      exact this
    · have : HasVal (w.restrictAlong φ hφi) (CNTAux.yF q k) (b ^ q ^ 2) := by
        rw [hasVal_restrictAlong_iff, hφy]; exact hb.pow _
      exact this
  have hη := ηk_ne_zero q k ζ
  have hfa' : a ^ q ^ 2 = (ηk q k ζ)⁻¹ * a := by
    rw [eq_inv_mul_iff_mul_eq₀ hη]; exact hfa
  have hfb' : b ^ q ^ 2 = (ηk q k ζ)⁻¹ * b := by
    rw [eq_inv_mul_iff_mul_eq₀ hη]; exact hfb
  have h2 : ση q k ζ • w = v := by
    apply huniq
    constructor
    · have : HasVal (ση q k ζ • w) (CNTAux.xF q k) (a ^ q ^ 2) := by
        rw [hasVal_smul_iff, ση_symm_xF, hfa']; exact ha.const_mul _
      exact this
    · have : HasVal (ση q k ζ • w) (CNTAux.yF q k) (b ^ q ^ 2) := by
        rw [hasVal_smul_iff, ση_symm_yF, hfb']; exact hb.const_mul _
      exact this
  rw [Rel, h1, h2]

include hφx hφy in

noncomputable def affEquiv :
    {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w ∧ Aff q k w} ≃ ↥(S q k ζ) where
  toFun w := ⟨(w.1.evalAt (CNTAux.xF q k), w.1.evalAt (CNTAux.yF q k)), by
    obtain ⟨a, b, ha, hb, hab, hfa, hfb⟩ :=
      values_mem_affineFixed q k ζ φ hφi hφx hφy (isRational q k w.1) w.2.2.1 w.2.2.2 w.2.1
    have ha' := ha.unique (hasVal_evalAt q k (isRational q k w.1) w.2.2.1)
    have hb' := hb.unique (hasVal_evalAt q k (isRational q k w.1) w.2.2.2)
    subst ha' hb'
    exact ⟨hab, hfa, hfb⟩⟩
  invFun p := ⟨Classical.choose (GenusAux.existsUnique_place_of_point q k p.2.1).exists, by
    have hc := Classical.choose_spec (GenusAux.existsUnique_place_of_point q k p.2.1).exists
    refine ⟨rel_of_hasVal q k φ hφi hφx hφy ζ (a := p.1.1) (b := p.1.2) p.2 hc.1 hc.2, ?_, ?_⟩
    · exact HasVal.mem hc.1
    · exact HasVal.mem hc.2⟩
  left_inv w := by
    apply Subtype.ext
    have hrat := isRational q k w.1
    have hu := GenusAux.existsUnique_place_of_point q k
      (a := w.1.evalAt (CNTAux.xF q k)) (b := w.1.evalAt (CNTAux.yF q k))

    obtain ⟨a, b, ha, hb, hab, -, -⟩ :=
      values_mem_affineFixed q k ζ φ hφi hφx hφy hrat w.2.2.1 w.2.2.2 w.2.1
    have ha' := ha.unique (hasVal_evalAt q k hrat w.2.2.1)
    have hb' := hb.unique (hasVal_evalAt q k hrat w.2.2.2)
    subst ha' hb'
    have hc := Classical.choose_spec (hu hab).exists
    exact (hu hab).unique hc ⟨hasVal_evalAt q k hrat w.2.2.1, hasVal_evalAt q k hrat w.2.2.2⟩
  right_inv p := by
    obtain ⟨⟨a, b⟩, hp⟩ := p
    apply Subtype.ext
    simp only
    have hc := Classical.choose_spec (GenusAux.existsUnique_place_of_point q k hp.1).exists
    set w := Classical.choose (GenusAux.existsUnique_place_of_point q k hp.1).exists
    have hrat := isRational q k w
    ext
    · exact (hasVal_evalAt q k hrat (HasVal.mem hc.1)).unique hc.1
    · exact (hasVal_evalAt q k hrat (HasVal.mem hc.2)).unique hc.2

#print "MAX-aff-ok"
end
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

end MaxAux
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"
end DrinfeldCurve
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_mu drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext mk_drinfeldPoly x y relation muAction muAction_x muAction_y one_mem_hSubgroup_of_mem isCurveOver_drinfeldFunctionField finite_and_ncard_setOf_twistedFrobenius_affineFixed"
p2m_open "DrinfeldCurve"
namespace MaxAux

open AlgebraicCurve DrinfeldCurve.CNTAux
open scoped Classical Pointwise

set_option linter.unusedSectionVars false

section Infty
variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]
  (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
  (hφx : φ (CNTAux.xF q k) = CNTAux.xF q k ^ q ^ 2) (hφy : φ (CNTAux.yF q k) = CNTAux.yF q k ^ q ^ 2)
  (ζ : rootsOfUnity (q + 1) (GaloisField q 2))

include hφx in

theorem hasVal_x_restrictAlong {w : Place k (drinfeldFunctionField q k)} {a : k} (ha : HasVal w (CNTAux.xF q k) a) :
    HasVal (w.restrictAlong φ hφi) (CNTAux.xF q k) (a ^ q ^ 2) := by
  rw [hasVal_restrictAlong_iff, hφx]; exact ha.pow _

include hφy in

theorem hasVal_y_restrictAlong {w : Place k (drinfeldFunctionField q k)} {b : k} (hb : HasVal w (CNTAux.yF q k) b) :
    HasVal (w.restrictAlong φ hφi) (CNTAux.yF q k) (b ^ q ^ 2) := by
  rw [hasVal_restrictAlong_iff, hφy]; exact hb.pow _

theorem hasVal_x_smul {w : Place k (drinfeldFunctionField q k)} {a : k} (ha : HasVal w (CNTAux.xF q k) a) :
    HasVal (ση q k ζ • w) (CNTAux.xF q k) ((ηk q k ζ)⁻¹ * a) := by
  rw [hasVal_smul_iff, ση_symm_xF]; exact ha.const_mul _

theorem hasVal_y_smul {w : Place k (drinfeldFunctionField q k)} {b : k} (hb : HasVal w (CNTAux.yF q k) b) :
    HasVal (ση q k ζ • w) (CNTAux.yF q k) ((ηk q k ζ)⁻¹ * b) := by
  rw [hasVal_smul_iff, ση_symm_yF]; exact hb.const_mul _

include hφx hφy in
theorem phi_uFF : φ (GenusAux.uFF q k) = GenusAux.uFF q k ^ q ^ 2 := by
  rw [uFF_eq, map_div₀, hφx, hφy, div_pow]

theorem sigma_symm_uFF : (ση q k ζ).symm (GenusAux.uFF q k) = GenusAux.uFF q k := by
  have hη : algebraMap k (drinfeldFunctionField q k) (ηk q k ζ)⁻¹ ≠ 0 :=
    (map_ne_zero _).mpr (inv_ne_zero (ηk_ne_zero q k ζ))
  rw [uFF_eq, map_div₀, ση_symm_xF, ση_symm_yF, mul_div_mul_left _ _ hη]

theorem uFF_sub_algebraMap_ne_zero (a : k) : GenusAux.uFF q k - algebraMap k (drinfeldFunctionField q k) a ≠ 0 := by
  intro h
  obtain ⟨v, hv, -⟩ := GenusAux.existsUnique_uFF_not_mem q k
  exact hv (sub_eq_zero.mp h ▸ v.algebraMap_mem' a)

omit hq [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (CoordRing q k)] in
theorem ord_pow_pos_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) {n : ℕ}
    (hn : 0 < n) : 0 < v.ord (f ^ n) ↔ 0 < v.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; positivity

omit hq [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (CoordRing q k)] in
theorem pow_mem_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) {n : ℕ}
    (hn : 0 < n) : f ^ n ∈ v.toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [Place.mem_iff_ord_nonneg _ (pow_ne_zero _ hf), Place.mem_iff_ord_nonneg _ hf, ← zpow_natCast, Place.ord_zpow]
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; positivity

include hφx hφy in

theorem rel_of_not_aff {w : Place k (drinfeldFunctionField q k)} (hw : ¬ Aff q k w) : Rel q k φ hφi ζ w := by
  haveI := charP_F q k
  have hw' : GenusAux.xF q k ∉ w.toValuationSubring ∨ GenusAux.yF q k ∉ w.toValuationSubring := not_and_or.mp hw
  have hu0 : GenusAux.uFF q k ≠ 0 := GenusAux.uFF_ne_zero q k
  have hq2 : 0 < q ^ 2 := pow_pos hq.out.pos 2
  rcases (GenusAux.not_mem_or_not_mem_iff_direction q k w).mp hw' with hinf | ⟨a, ha, hpos⟩
  ·
    refine GenusAux.eq_of_uFF_not_mem q k (v := w.restrictAlong φ hφi) (w := ση q k ζ • w) ?_ ?_
    · change φ (GenusAux.uFF q k) ∉ w.toValuationSubring
      rw [phi_uFF q k φ hφx hφy, pow_mem_iff w hu0 hq2]
      exact hinf
    · rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      change (ση q k ζ).symm (GenusAux.uFF q k) ∉ w.toValuationSubring
      rw [sigma_symm_uFF]
      exact hinf
  ·
    have hne := uFF_sub_algebraMap_ne_zero q k a
    have haq2 : a ^ q ^ 2 = a := by rw [pow_two, pow_mul, ha, ha]
    refine GenusAux.eq_of_ord_uFF_sub_pos q k ha (v := w.restrictAlong φ hφi) (w := ση q k ζ • w) ?_ ?_
    · rw [← GenusAux.mem_nonunits_iff_ord_pos _ hne]
      change GenusAux.uFF q k - algebraMap k _ a ∈ (w.toValuationSubring.comap φ.toRingHom).nonunits
      rw [mem_nonunits_comap_iff]
      change φ (GenusAux.uFF q k - algebraMap k _ a) ∈ w.toValuationSubring.nonunits
      rw [map_sub, AlgHom.commutes, phi_uFF q k φ hφx hφy]
      have hpow : GenusAux.uFF q k ^ q ^ 2 - algebraMap k (drinfeldFunctionField q k) a =
          (GenusAux.uFF q k - algebraMap k (drinfeldFunctionField q k) a) ^ q ^ 2 := by
        rw [sub_pow_char_pow, ← map_pow, haq2]
      rw [hpow, GenusAux.mem_nonunits_iff_ord_pos _ (pow_ne_zero _ hne), ord_pow_pos_iff w hne hq2]
      exact hpos
    · rw [← GenusAux.mem_nonunits_iff_ord_pos _ hne, Place.smul_toValuationSubring, mem_nonunits_smul_iff,
        map_sub, AlgEquiv.commutes, sigma_symm_uFF, GenusAux.mem_nonunits_iff_ord_pos _ hne]
      exact hpos

#print "MAX-inf-ok"
end Infty
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

section Count
variable (q : ℕ) [hq : Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
  [IsDomain (CoordRing q k)]
  (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
  (hφx : φ (CNTAux.xF q k) = CNTAux.xF q k ^ q ^ 2) (hφy : φ (CNTAux.yF q k) = CNTAux.yF q k ^ q ^ 2)
  (ζ : rootsOfUnity (q + 1) (GaloisField q 2))

include hφx hφy in

theorem natCard_rel_not_aff :
    Nat.card {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w ∧ ¬ Aff q k w} = q + 1 := by
  rw [← GenusAux.natCard_setOf_not_mem_or_not_mem q k]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun w => ?_)
  rw [Aff, not_and_or]
  exact ⟨fun h => h.2, fun h => ⟨rel_of_not_aff q k φ hφi hφx hφy ζ (not_and_or.mpr h), h⟩⟩

include hφx hφy in

theorem natCard_rel (hS : (S q k ζ).Finite) (hcard : (S q k ζ).ncard = q ^ 3 - q) :
    Nat.card {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w} = q ^ 3 + 1 := by
  haveI : Finite ↥(S q k ζ) := hS.to_subtype
  haveI hfA : Finite {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w ∧ Aff q k w} :=
    Finite.of_equiv _ (affEquiv q k φ hφi hφx hφy ζ).symm
  haveI hfI : Finite {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w ∧ ¬ Aff q k w} := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_rel_not_aff q k φ hφi hφx hφy ζ]
    omega
  have hsplit : Nat.card {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w} =
      Nat.card {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w ∧ Aff q k w} +
        Nat.card {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w ∧ ¬ Aff q k w} := by
    rw [← Nat.card_sum]
    apply Nat.card_congr
    exact ((Equiv.sumCompl (fun w : {w : Place k (drinfeldFunctionField q k) // Rel q k φ hφi ζ w} => Aff q k w.1)).symm.trans
      (Equiv.sumCongr
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun w => Rel q k φ hφi ζ w) (fun w => Aff q k w))
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun w => Rel q k φ hφi ζ w) (fun w => ¬ Aff q k w))))
  rw [hsplit, natCard_rel_not_aff q k φ hφi hφx hφy ζ, Nat.card_congr (affEquiv q k φ hφi hφx hφy ζ),
    Nat.card_coe_set_eq, hcard]
  have : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
  omega

#print "MAX-count-ok"
end Count
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

end MaxAux
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"
end DrinfeldCurve
p2m_reactivate "P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve"

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul.DrinfeldCurve in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) (hζ : ((ζ : (GaloisField q 2)ˣ) : GaloisField q 2) = -1) :
    Nat.card {w : AlgebraicCurve.Place k (drinfeldFunctionField q k) //
        AlgebraicCurve.Place.restrictAlong φ hφi w =
          hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩ • w} = q ^ 3 + 1 := by
  obtain ⟨hfin, hneg, -⟩ := DrinfeldCurve.finite_and_ncard_setOf_twistedFrobenius_affineFixed q k ζ
  exact DrinfeldCurve.MaxAux.natCard_rel q k φ hφi hφx hφy ζ hfin (hneg hζ)

end S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul
end P2MW
export P2MW.S_DrinfeldCurve_natCard_place_restrictAlong_eq_neg_one_smul (solution)
