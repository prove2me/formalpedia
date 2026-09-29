-- Prove2me | solution 1 for DrinfeldCurve.isCurveOver_fixedField_hFunctionFieldAction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6c89122b-bb2e-507b-93bf-9ee39d4c475d

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_minpoly_eq_X_pow_sub_C_of_isCoprime_apply
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_mu drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext x y relation natCard_rootsOfUnity_galoisField_two scalarOf muAction muAction_x muAction_y one_mem_hSubgroup_of_mem"
p2m_open "DrinfeldCurve"

namespace GenusAux

open AlgebraicCurve Polynomial

section Basic

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsDomain (CoordRing q k)]

theorem two_le_q : 2 ≤ q := (Fact.out : q.Prime).two_le

theorem one_lt_q : 1 < q := (Fact.out : q.Prime).one_lt

noncomputable def xF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)

noncomputable def yF : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)

theorem relF : xF q k * yF q k ^ q - xF q k ^ q * yF q k = 1 := by
  have h := congrArg (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) (relation q k)
  first | exact h | simpa only [map_sub, map_mul, map_pow, map_one] using h | simpa only [map_sub, map_mul, map_pow, map_one, xF, yF] using h

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

theorem finSuccEquiv_one_sub_drinfeldPoly :
    MvPolynomial.finSuccEquiv k 1 (1 - drinfeldPoly q k) =
      Polynomial.trinomial 0 1 q (1 : MvPolynomial (Fin 1) k) (-(MvPolynomial.X 0) ^ q) (MvPolynomial.X 0) := by
  have hX0 : MvPolynomial.finSuccEquiv k 1 (MvPolynomial.X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
  have hX1 : MvPolynomial.finSuccEquiv k 1 (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  simp only [drinfeldPoly, map_sub, map_one, map_mul, map_pow, hX0, hX1, Polynomial.trinomial_def, map_neg]
  ring

theorem eq_zero_of_aeval_X_one_mem (p : k[X])
    (hp : Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) p ∈ drinfeldIdeal q k) : p = 0 := by
  have hq := two_le_q q
  set e := MvPolynomial.finSuccEquiv k 1 with he
  rw [drinfeldIdeal, Ideal.mem_span_singleton] at hp
  obtain ⟨g, hg⟩ := hp
  have hX1 : e (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have hlhs : e (Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) p) =
      Polynomial.C (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 1) k) p) := by
    rw [← Polynomial.aeval_algHom_apply, hX1, ← Polynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply]
  have hf : e (drinfeldPoly q k - 1) =
      -Polynomial.trinomial 0 1 q (1 : MvPolynomial (Fin 1) k) (-(MvPolynomial.X 0) ^ q) (MvPolynomial.X 0) := by
    rw [← finSuccEquiv_one_sub_drinfeldPoly, ← map_neg, neg_sub]
  have hdeg : (e (drinfeldPoly q k - 1)).natDegree = q := by
    rw [hf, Polynomial.natDegree_neg]
    exact Polynomial.trinomial_natDegree zero_lt_one (by omega) (MvPolynomial.X_ne_zero 0)
  have hf0 : e (drinfeldPoly q k - 1) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  set a := Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 1) k) p with ha
  have hprod : Polynomial.C a = e (drinfeldPoly q k - 1) * e g := by
    rw [← hlhs, hg, map_mul]
  have ha0 : a = 0 := by
    by_contra ha0
    have hg0 : e g ≠ 0 := by
      intro h0
      rw [h0, mul_zero, Polynomial.C_eq_zero] at hprod
      exact ha0 hprod
    have h := congrArg Polynomial.natDegree hprod
    rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hf0 hg0, hdeg] at h
    omega
  have hinj : Function.Injective (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 1) k)) :=
    transcendental_iff_injective.mp ((MvPolynomial.algebraicIndependent_X (Fin 1) k).transcendental 0)
  exact hinj (by rw [← ha, ha0, map_zero])

theorem transcendental_yF : Transcendental k (yF q k) := by
  rw [transcendental_iff_injective]
  intro p₁ p₂ h
  rw [← sub_eq_zero, ← map_sub] at h
  rw [← sub_eq_zero]
  set p := p₁ - p₂
  have h1 : Polynomial.aeval (yF q k) p =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (Polynomial.aeval (y q k) p) := by
    rw [yF, Polynomial.aeval_algebraMap_apply]
  rw [h1, map_eq_zero_iff _ (IsFractionRing.injective (CoordRing q k) (drinfeldFunctionField q k))] at h
  have h2 : Polynomial.aeval (y q k) p = mk q k (Polynomial.aeval (MvPolynomial.X 1) p) := by
    rw [y, ← Polynomial.aeval_algHom_apply]
  rw [h2] at h
  change Ideal.Quotient.mk (drinfeldIdeal q k) (Polynomial.aeval (MvPolynomial.X 1) p) = 0 at h
  exact eq_zero_of_aeval_X_one_mem q k p (Ideal.Quotient.eq_zero_iff_mem.mp h)

theorem transcendental_uFF : Transcendental k (uFF q k) := by
  intro halg
  have hint : IsIntegral k (uFF q k) := halg.isIntegral
  have h1 : IsIntegral k (uFF q k - uFF q k ^ q) := hint.sub (hint.pow q)
  have h2 : IsIntegral k (wFF q k) := by
    refine IsIntegral.of_pow (Nat.succ_pos q) ?_
    rw [wFF_pow]
    exact h1
  have h3 : IsIntegral k (yF q k) := by
    rw [yF_eq]
    exact h2.inv
  exact transcendental_yF q k h3.isAlgebraic

end Basic

section Char

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

theorem charP_of_galoisField : CharP k q := charP_of_injective_algebraMap' (GaloisField q 2) q

theorem cast_q_eq_zero : (q : k) = 0 := by
  haveI := charP_of_galoisField q k
  exact CharP.cast_eq_zero k q

theorem cast_q_add_one_ne_zero : ((q + 1 : ℕ) : k) ≠ 0 := by
  rw [Nat.cast_add, cast_q_eq_zero q k, zero_add, Nat.cast_one]
  exact one_ne_zero

end Char

section MuAction

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

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

private noncomputable def _root_.DrinfeldCurve.GenusAux.GC : Subgroup (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :=
  Subgroup.closure (Set.range fun ζ : ↥C =>
    hFunctionFieldAction q k ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
      one_mem_hSubgroup_of_mem q ζ⟩)

p2m_export "DrinfeldCurve.GenusAux" "GC"
theorem hFunctionFieldAction_mu_eq_muF (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    hFunctionFieldAction q k ⟨(1, (ζ : (GaloisField q 2)ˣ)), one_mem_hSubgroup_of_mem q ζ⟩ = muF q k ζ := by
  rw [muF_apply]
  exact hFunctionFieldAction_mu q k ζ

theorem GC_eq_map : GC q k C = C.map (muF q k) := by
  have hrange : (Set.range fun ζ : ↥C =>
      hFunctionFieldAction q k ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
        one_mem_hSubgroup_of_mem q ζ⟩) = (C.map (muF q k) : Set (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)) := by
    ext σ
    simp only [Set.mem_range, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨ζ, rfl⟩
      exact ⟨ζ, ζ.2, (hFunctionFieldAction_mu_eq_muF q k ζ).symm⟩
    · rintro ⟨ζ, hζ, rfl⟩
      exact ⟨⟨ζ, hζ⟩, hFunctionFieldAction_mu_eq_muF q k ζ⟩
  rw [GC, hrange, Subgroup.closure_eq]

private noncomputable def _root_.DrinfeldCurve.GenusAux.EC : IntermediateField k (drinfeldFunctionField q k) := IntermediateField.fixedField (GC q k C)

p2m_export "DrinfeldCurve.GenusAux" "EC"
theorem mem_EC_iff (z : drinfeldFunctionField q k) : z ∈ EC q k C ↔ ∀ ζ ∈ C, muF q k ζ z = z := by
  rw [EC, IntermediateField.mem_fixedField_iff, GC_eq_map]
  constructor
  · intro h ζ hζ
    exact h (muF q k ζ) (Subgroup.mem_map_of_mem _ hζ)
  · rintro h σ ⟨ζ, hζ, rfl⟩
    exact h ζ hζ

theorem uFF_mem_EC : uFF q k ∈ EC q k C :=
  (mem_EC_iff q k C _).mpr fun ζ _ => muF_uFF q k ζ

theorem wFF_pow_natCard_mem_EC : wFF q k ^ Nat.card C ∈ EC q k C :=
  (mem_EC_iff q k C _).mpr fun _ hζ => muF_wFF_pow_natCard q k C hζ

theorem natCard_GC : Nat.card (GC q k C) = Nat.card C := by
  rw [GC_eq_map]
  exact Subgroup.card_map_of_injective (muF_injective q k)

scoped instance finite_GC : Finite (GC q k C) := by
  rw [GC_eq_map]
  exact Finite.of_surjective (fun c : C => (⟨muF q k c, Subgroup.mem_map_of_mem _ c.2⟩ : C.map (muF q k))) (by
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

theorem scalarOf_pow_card_galoisField (ζ : (GaloisField q 2)ˣ) : scalarOf q k ζ ^ q ^ 2 = scalarOf q k ζ := by
  rw [scalarOf, ← map_pow]
  congr 1
  haveI := Fintype.ofFinite (GaloisField q 2)
  have hc : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card q 2 two_ne_zero
  rw [← hc, FiniteField.pow_card]

theorem sF_pow_card_galoisField (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : sF q k ζ ^ q ^ 2 = sF q k ζ := by
  rw [sF, ← map_pow, scalarOf_pow_card_galoisField]

theorem comp_muF_eq_muF_comp (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)
    (hx : φ (xF q k) = xF q k ^ q ^ 2) (hy : φ (yF q k) = yF q k ^ q ^ 2)
    (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    φ.comp (muF q k ζ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) =
      (muF q k ζ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k).comp φ := by

  have hA : (φ.comp (muF q k ζ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)).comp
        (IsScalarTower.toAlgHom k (CoordRing q k) (drinfeldFunctionField q k)) =
      ((muF q k ζ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k).comp φ).comp
        (IsScalarTower.toAlgHom k (CoordRing q k) (drinfeldFunctionField q k)) := by
    apply algHom_ext q k
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · show φ (muF q k ζ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k (MvPolynomial.X 0)))) =
        muF q k ζ (φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k (MvPolynomial.X 0))))
      change φ (muF q k ζ (xF q k)) = muF q k ζ (φ (xF q k))
      rw [muF_xF, map_mul, hx, map_pow, muF_xF, mul_pow, sF_pow_card_galoisField, sF, AlgHom.commutes]
    · show φ (muF q k ζ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k (MvPolynomial.X 1)))) =
        muF q k ζ (φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k (MvPolynomial.X 1))))
      change φ (muF q k ζ (yF q k)) = muF q k ζ (φ (yF q k))
      rw [muF_yF, map_mul, hy, map_pow, muF_yF, mul_pow, sF_pow_card_galoisField, sF, AlgHom.commutes]

  have hR : (φ.comp (muF q k ζ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) :
        drinfeldFunctionField q k →+* drinfeldFunctionField q k) =
      ((muF q k ζ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k).comp φ :
        drinfeldFunctionField q k →+* drinfeldFunctionField q k) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
    have := congrArg (fun ψ : CoordRing q k →ₐ[k] drinfeldFunctionField q k => (ψ : CoordRing q k →+* drinfeldFunctionField q k)) hA
    exact this
  exact AlgHom.ext fun z => RingHom.congr_fun hR z

theorem map_mem_EC (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)
    (hx : φ (xF q k) = xF q k ^ q ^ 2) (hy : φ (yF q k) = yF q k ^ q ^ 2)
    (z : drinfeldFunctionField q k) (hz : z ∈ EC q k C) : φ z ∈ EC q k C := by
  rw [mem_EC_iff] at hz ⊢
  intro ζ hζ
  have h := congrArg (fun ψ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k => ψ z)
    (comp_muF_eq_muF_comp q k φ hx hy ζ)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom] at h
  rw [← h, hz ζ hζ]

theorem map_mem_EC' (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)
    (hx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (z : drinfeldFunctionField q k) (hz : z ∈ EC q k C) : φ z ∈ EC q k C :=
  map_mem_EC q k C φ hx hy z hz

end MuAction

section Presentation

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

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

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

variable (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))

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

noncomputable def uC : EC q k C := ⟨uFF q k, uFF_mem_EC q k C⟩

@[scoped simp] theorem coe_uC : (uC q k C : drinfeldFunctionField q k) = uFF q k := rfl

theorem transcendental_uC : Transcendental k (uC q k C) := fun halg =>
  transcendental_uFF q k (halg.algHom (EC q k C).val)

theorem phiC_X' : phiC q k C RatFunc.X = uC q k C := phiC_X q k C

theorem finiteDimensional_adjoin_uC :
    FiniteDimensional (IntermediateField.adjoin k ({uC q k C} : Set (EC q k C))) (EC q k C) := by
  set L := IntermediateField.adjoin k ({uC q k C} : Set (EC q k C)) with hL
  let ψ : RatFunc k →ₐ[k] L := (RatFunc.algEquivOfTranscendental (uC q k C) (transcendental_uC q k C)).toAlgHom
  have hψ : ((algebraMap L (EC q k C)).comp (ψ : RatFunc k →+* L)) = (phiC q k C : RatFunc k →+* EC q k C) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    refine RingHom.ext fun p => ?_
    show ((ψ (algebraMap k[X] (RatFunc k) p) : L) : EC q k C) = phiC q k C (algebraMap k[X] (RatFunc k) p)
    have h1 : ψ (algebraMap k[X] (RatFunc k) p) = Polynomial.aeval (IntermediateField.AdjoinSimple.gen k (uC q k C)) p :=
      RatFunc.algEquivOfTranscendental_algebraMap _ _ p
    rw [h1, ← IntermediateField.coe_val, ← Polynomial.aeval_algHom_apply, IntermediateField.coe_val,
      IntermediateField.AdjoinSimple.coe_gen]
    apply Subtype.ext
    rw [coe_phiC, phi_algebraMap, ← IntermediateField.coe_val, ← Polynomial.aeval_algHom_apply, IntermediateField.coe_val,
      coe_uC]
  letI : Algebra (RatFunc k) L := (ψ : RatFunc k →+* L).toAlgebra
  haveI : IsScalarTower (RatFunc k) L (EC q k C) :=
    IsScalarTower.of_algebraMap_eq fun f => (RingHom.congr_fun hψ f).symm
  exact Module.Finite.of_restrictScalars_finite (RatFunc k) L (EC q k C)

private theorem _root_.DrinfeldCurve.GenusAux.exists_transcendental_finiteDimensional_EC :
    ∃ t : EC q k C, Transcendental k t ∧
      FiniteDimensional (IntermediateField.adjoin k ({t} : Set (EC q k C))) (EC q k C) :=
  ⟨uC q k C, transcendental_uC q k C, finiteDimensional_adjoin_uC q k C⟩

p2m_export "DrinfeldCurve.GenusAux" "exists_transcendental_finiteDimensional_EC"
end QuotientPresentation

end GenusAux
p2m_reactivate "P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction.DrinfeldCurve.GenusAux"

namespace TR

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

private noncomputable abbrev _root_.DrinfeldCurve.TR.GC (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    Subgroup (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :=
  Subgroup.closure (Set.range fun ζ : ↥C =>
    hFunctionFieldAction q k ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
      one_mem_hSubgroup_of_mem q ζ⟩)

p2m_export "DrinfeldCurve.TR" "GC"

private noncomputable abbrev _root_.DrinfeldCurve.TR.EC (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    IntermediateField k (drinfeldFunctionField q k) :=
  IntermediateField.fixedField (GC q k C)

p2m_export "DrinfeldCurve.TR" "EC"
variable (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))

theorem GC_eq : TR.GC q k C = GenusAux.GC q k C := rfl

theorem EC_eq : TR.EC q k C = GenusAux.EC q k C := rfl

private theorem _root_.DrinfeldCurve.TR.map_mem_EC (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    {z : drinfeldFunctionField q k} (hz : z ∈ TR.EC q k C) : φ z ∈ TR.EC q k C :=
  GenusAux.map_mem_EC q k C φ hφx hφy z hz

p2m_export "DrinfeldCurve.TR" "map_mem_EC"

private theorem _root_.DrinfeldCurve.TR.exists_transcendental_finiteDimensional_EC :
    ∃ t : ↥(TR.EC q k C), Transcendental k t ∧
      FiniteDimensional (IntermediateField.adjoin k ({t} : Set (TR.EC q k C))) (TR.EC q k C) :=
  GenusAux.exists_transcendental_finiteDimensional_EC q k C

p2m_export "DrinfeldCurve.TR" "exists_transcendental_finiteDimensional_EC"
end TR
p2m_reactivate "P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction.DrinfeldCurve.GenusAux"

namespace GenusAux

end GenusAux
p2m_reactivate "P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction.DrinfeldCurve.GenusAux"

end DrinfeldCurve
p2m_reactivate "P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction.DrinfeldCurve.GenusAux P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction.DrinfeldCurve"

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction.DrinfeldCurve in

theorem solution (q : ℕ) [Fact q.Prime] (k : Type) [Field k]
    [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (CoordRing q k)]
    (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    AlgebraicCurve.IsCurveOver k
      ↥(IntermediateField.fixedField (Subgroup.closure (Set.range fun ζ : ↥C =>
        hFunctionFieldAction q k ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
          one_mem_hSubgroup_of_mem q ζ⟩))) := by
  change AlgebraicCurve.IsCurveOver k ↥(TR.EC q k C)
  obtain ⟨t, ht, hfd⟩ := TR.exists_transcendental_finiteDimensional_EC q k C
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht hfd

example (q : ℕ) [Fact q.Prime] (k : Type) [Field k]
    [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    AlgebraicCurve.IsCurveOver k
      ↥(IntermediateField.fixedField (Subgroup.closure (Set.range fun ζ : C =>
            DrinfeldCurve.hFunctionFieldAction q k ⟨_, DrinfeldCurve.one_mem_hSubgroup_of_mem q ζ⟩))) := by
  haveI := solution q k C
  infer_instance

end S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction
end P2MW
export P2MW.S_DrinfeldCurve_isCurveOver_fixedField_hFunctionFieldAction (solution)
