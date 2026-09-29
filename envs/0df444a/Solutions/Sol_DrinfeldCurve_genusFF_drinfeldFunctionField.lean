-- Prove2me | solution 1 for DrinfeldCurve.genusFF_drinfeldFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1c17c454-472f-536f-9c44-c030243bc14a

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_genusFF_drinfeldFunctionField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective x y relation isCurveOver_drinfeldFunctionField"
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

p2m_open "AlgebraicCurve~genus AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
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

p2m_open "AlgebraicCurve~genus AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
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

theorem finsum_ramificationIndex_sub_one :
    ∑ᶠ w : Place k (drinfeldFunctionField q k), ((w.ramificationIndex (RatFunc k) : ℤ) - 1) = q * (q + 1) := by
  rw [finsum_eq_sum_sum_fiber (S q k) _ (fun w hw => by rw [ramificationIndex_eq_of_not_mem q k w hw]; simp)]
  have h : ∀ v ∈ S q k, ∑ w ∈ v.fiber (drinfeldFunctionField q k), ((w.ramificationIndex (RatFunc k) : ℤ) - 1) = q := by
    intro v hv
    rw [Finset.sum_congr rfl (fun w hw => by
      rw [ramificationIndex_eq_of_mem q k w ((Place.mem_fiber.mp hw).symm ▸ hv)])]
    rw [Finset.sum_const, card_fiber_eq_one q k hv]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_S]
  push_cast
  ring

theorem two_mul_genusFF : 2 * (genusFF k (drinfeldFunctionField q k) : ℤ) = q * q - q := by
  have hRH := finsum_ramificationIndex_ratFunc_sub_one_eq_of_tame (K := k) (F := drinfeldFunctionField q k)
    (natCast_ramificationIndex_ne_zero q k)
  rw [finsum_ramificationIndex_sub_one, finrank_ratFunc] at hRH
  push_cast at hRH
  linarith

theorem genusFF_eq : genusFF k (drinfeldFunctionField q k) = q * (q - 1) / 2 := by
  have h1 : 1 ≤ q := hq.out.one_le
  have h2 := two_mul_genusFF q k
  have h3 : 2 * genusFF k (drinfeldFunctionField q k) = q * (q - 1) := by
    zify [h1]
    linarith
  symm
  apply Nat.div_eq_of_eq_mul_left two_pos
  rw [Nat.mul_comm _ 2]
  exact h3.symm

end CountB

end GenusAux
p2m_reactivate "P2MW.S_DrinfeldCurve_genusFF_drinfeldFunctionField.DrinfeldCurve.GenusAux"

end DrinfeldCurve
p2m_reactivate "P2MW.S_DrinfeldCurve_genusFF_drinfeldFunctionField.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_genusFF_drinfeldFunctionField.DrinfeldCurve"

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_genusFF_drinfeldFunctionField.DrinfeldCurve in

theorem solution (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]
    [IsAlgClosed k] [IsDomain (CoordRing q k)] :
    AlgebraicCurve.genusFF k (drinfeldFunctionField q k) = q * (q - 1) / 2 := by
  exact DrinfeldCurve.GenusAux.genusFF_eq q k

end S_DrinfeldCurve_genusFF_drinfeldFunctionField
end P2MW
export P2MW.S_DrinfeldCurve_genusFF_drinfeldFunctionField (solution)
