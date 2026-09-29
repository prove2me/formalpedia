-- Prove2me | solution 1 for AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_flat_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2bfc41a4-b8e8-524a-97b4-4819e40456b8

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
import Theorems.Thm_AutomorphicForm_LocalIntertwining_exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion
import Theorems.Thm_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
import Theorems.Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
import Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_flat_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel FLT.SmoothVectors NumberField.AdelicBox
open scoped NNReal

namespace WeylFlatContinuation
namespace Local

private theorem localFactor_meromorphic (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hcond : ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (m : ℕ) (hm : 1 ≤ m) (A B : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    ∃ Mv : ℂ → ℂ, MeromorphicOn Mv Set.univ ∧ ∀ s : ℂ, 1 / 2 < s.re →
      Mv s = ((μv.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹
        * ∫ y, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A y
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt
                    (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                  * B y⁻¹) y) ∂μv := by
  have hunit : ∀ t : (v.adicCompletion F)ˣ,
      ‖((NumberField.TateGlobal.localChar (μ * ν⁻¹) v t : ℂˣ) : ℂ)‖ = 1 := by
    intro t
    rw [NumberField.TateGlobal.localChar_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
      Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hμ _, hν _, inv_one, mul_one]
  have hN : 1 < Ideal.absNorm v.asIdeal := by
    refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, ?_⟩
    · exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    · exact fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hregion : ∀ s : ℂ, 1 / 2 < s.re →
      ‖((NumberField.TateGlobal.localChar (μ * ν⁻¹) v ϖ : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
    intro s hs
    rw [norm_mul, hunit, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have hre : (-(2 * s)).re = -(2 * s.re) := by simp
    rw [hre]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) (by linarith)
  obtain ⟨M, hM, hMs⟩ :=
    AutomorphicForm.LocalIntertwining.exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion
      F v μv ϖ hϖ (NumberField.TateGlobal.localChar (μ * ν⁻¹) v) hcond m hm
      (fun _ => A) (fun _ => hA) (fun _ => differentiable_const _)
      (fun _ => B) (fun _ => hB) (fun _ => differentiable_const _)
  refine ⟨fun s =>
      ((μv.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ * M s,
    (MeromorphicOn.const _).mul hM, fun s hs => ?_⟩
  show _ * M s = _
  rw [hMs s (hregion s hs)]

end WeylFlatContinuation.Local

namespace WeylFlatContinuation
namespace Local

variable (F : Type) [Field F] [NumberField F]

private theorem one_sub_mul_natCast_cpow_neg_ne_zero {a : ℂ} (ha : ‖a‖ ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    {z : ℂ} (hz : 0 < z.re) : (1 : ℂ) - a * (n : ℂ) ^ (-z) ≠ 0 := by
  intro h
  have h1 : a * (n : ℂ) ^ (-z) = 1 := by linear_combination -h
  have hnorm : ‖a * (n : ℂ) ^ (-z)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hpow : (n : ℝ) ^ (-z.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hn1 (by linarith)
    have hpos : 0 ≤ (n : ℝ) ^ (-z.re) := Real.rpow_nonneg (by positivity) _
    calc ‖a‖ * (n : ℝ) ^ (-z.re) ≤ 1 * (n : ℝ) ^ (-z.re) :=
          mul_le_mul_of_nonneg_right ha hpos
      _ = (n : ℝ) ^ (-z.re) := one_mul _
      _ < 1 := hpow
  rw [h1, norm_one] at hnorm
  exact lt_irrefl _ hnorm

private theorem multipliable_one_sub_mul_natCast_cpow_neg_and_tprod_ne_zero {ι : Type*}
    (N : ι → ℕ) (a : ι → ℂ) (z : ℂ)
    (hN : ∀ v, 2 ≤ N v) (ha : ∀ v, ‖a v‖ ≤ 1) (hz : 0 < z.re)
    (hsum : Summable fun v => ((N v : ℝ) ^ (-z.re))) :
    (Multipliable fun v => (1 : ℂ) - a v * (N v : ℂ) ^ (-z)) ∧
      ∏' v, ((1 : ℂ) - a v * (N v : ℂ) ^ (-z)) ≠ 0 := by
  set f : ι → ℂ := fun v => -(a v * (N v : ℂ) ^ (-z)) with hf_def
  have hshape : (fun v => (1 : ℂ) - a v * (N v : ℂ) ^ (-z)) = fun v => 1 + f v := by
    funext v; simp [hf_def, sub_eq_add_neg]
  have hnorm : Summable fun v => ‖f v‖ := by
    refine hsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    rw [hf_def]; dsimp only
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos (by have := hN v; omega), Complex.neg_re]
    have hpos : 0 ≤ (N v : ℝ) ^ (-z.re) := Real.rpow_nonneg (by positivity) _
    calc ‖a v‖ * (N v : ℝ) ^ (-z.re) ≤ 1 * (N v : ℝ) ^ (-z.re) :=
          mul_le_mul_of_nonneg_right (ha v) hpos
      _ = (N v : ℝ) ^ (-z.re) := one_mul _
  have hne : ∀ v, (1 : ℂ) + f v ≠ 0 := by
    intro v
    have := one_sub_mul_natCast_cpow_neg_ne_zero (ha v) (hN v) hz
    simpa [hf_def, sub_eq_add_neg] using this
  rw [hshape]
  exact ⟨multipliable_one_add_of_summable hnorm, tprod_one_add_ne_zero_of_summable hne hnorm⟩

private theorem summable_absNorm_rpow_neg (F : Type) [Field F] [NumberField F] {t : ℝ} (ht : 1 < t) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t) := by
  have H := NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top F ht
  set f : (HeightOneSpectrum (𝓞 F) →₀ ℕ) → ENNReal :=
    fun k => (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ENNReal) ^ (-t)) with hf
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 F) => Finsupp.single v (1 : ℕ) :=
    fun v w h => Finsupp.single_left_injective one_ne_zero h
  have hle : ∑' v : HeightOneSpectrum (𝓞 F), f (Finsupp.single v 1) ≤ ∑' k, f k :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj f
  have hfin : ∑' v : HeightOneSpectrum (𝓞 F), f (Finsupp.single v 1) ≠ ⊤ := (lt_of_le_of_lt hle H).ne
  have hsum := ENNReal.summable_toReal hfin
  refine hsum.congr fun v => ?_
  have hq : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [hf, Finsupp.prod_single_index, pow_zero, pow_one]
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

private theorem isUnitaryChar_mul_inv {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := by
  intro x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
    hμ x, hν x, inv_one, mul_one]

private theorem isIdeleClassChar_mul_inv {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν) :
    IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) := by
  intro u
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ u, hν u, inv_one, mul_one]

private theorem norm_localChar_eq_one {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 F) F χ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ‖((NumberField.TateGlobal.localChar χ v t : ℂˣ) : ℂ)‖ = 1 := by
  rw [NumberField.TateGlobal.localChar_apply]
  exact hχ _

private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem inv_div_inv_mul_cancel {x y : ℂ} (hx : x ≠ 0) : x⁻¹ / y⁻¹ * x = y := by
  rw [div_eq_mul_inv, inv_inv, mul_comm x⁻¹ y, mul_assoc, inv_mul_cancel₀ hx, mul_one]

private theorem eulerTail_meromorphic (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    (hχc : Continuous (μ * ν⁻¹))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ Q : ℂ → ℂ, MeromorphicOn Q Set.univ ∧ ∀ s : ℂ, 1 / 2 < s.re →
      (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))) ≠ 0 ∧
      Q s * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
        = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) := by
  obtain ⟨L, hL, hLs⟩ := NumberField.TateGlobal.exists_meromorphicOn_eq_partialEulerProduct F S ϖ hϖ (μ * ν⁻¹) hχc
    (isUnitaryChar_mul_inv F hμ hν) (isIdeleClassChar_mul_inv F hμic hνic)
  refine ⟨(fun s => L (2 * s)) / (fun s => L (2 * s + 1)), ?_, ?_⟩
  · refine MeromorphicOn.div ?_ ?_
    · intro x _
      exact (hL (2 * x) (Set.mem_univ _)).comp_analyticAt (g := fun s => 2 * s) (by fun_prop)
    · intro x _
      exact (hL (2 * x + 1) (Set.mem_univ _)).comp_analyticAt (g := fun s => 2 * s + 1) (by fun_prop)
  · intro s hs
    have h2 : (1 : ℝ) < (2 * s).re := by
      rw [show (2 * s).re = 2 * s.re by simp [Complex.mul_re]]
      linarith
    have h3 : (1 : ℝ) < (2 * s + 1).re := by
      rw [show (2 * s + 1).re = 2 * s.re + 1 by simp [Complex.add_re, Complex.mul_re]]
      linarith
    have hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 * s).re) :=
      (summable_absNorm_rpow_neg F h2).comp_injective Subtype.val_injective
    have hne := (multipliable_one_sub_mul_natCast_cpow_neg_and_tprod_ne_zero
      (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => Ideal.absNorm v.1.asIdeal)
      (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ))
      (2 * s) (fun v => two_le_absNorm F v.1)
      (fun v => (norm_localChar_eq_one F (isUnitaryChar_mul_inv F hμ hν) v.1 (ϖ v.1)).le) (by linarith) hsum).2
    refine ⟨hne, ?_⟩
    simp only [Pi.div_apply]
    rw [hLs (2 * s) h2, hLs (2 * s + 1) h3]
    exact inv_div_inv_mul_cancel hne

end WeylFlatContinuation.Local

namespace CpowClassification

open Complex intervalIntegral

private theorem exists_eq_exp_mul_of_continuous_of_add {h : ℝ → ℂ} (hc : Continuous h)
    (hadd : ∀ s t, h (s + t) = h s * h t) (h0 : h 0 = 1) :
    ∃ c : ℂ, ∀ t, h t = Complex.exp (c * t) := by
  set F : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, h u with hF_def
  have hF : ∀ t, HasDerivAt F (h t) t := fun t =>
    (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, F δ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hFz : F = fun _ => (0 : ℂ) := funext hcon
    have h1 : HasDerivAt F (h 0) 0 := hF 0
    rw [hFz] at h1
    have h2 : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (0 : ℂ) 0 := hasDerivAt_const _ _
    have := h1.unique h2
    rw [h0] at this
    exact one_ne_zero this
  have havg : ∀ t, h t * F δ = F (t + δ) - F t := by
    intro t
    have h1 : (∫ u in (0 : ℝ)..δ, h (t + u)) = h t * F δ := by
      have e1 : (∫ u in (0 : ℝ)..δ, h (t + u)) = ∫ u in (0 : ℝ)..δ, h t * h u :=
        intervalIntegral.integral_congr fun u _ => hadd t u
      rw [e1]
      exact intervalIntegral.integral_const_mul _ _
    have h2 : (∫ u in (0 : ℝ)..δ, h (t + u)) = ∫ u in t..(t + δ), h u := by
      simp
    have h3 : (∫ u in t..(t + δ), h u) = F (t + δ) - F t := by
      simp only [hF_def]
      rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
    rw [← h1, h2, h3]
  have hdiff : ∀ t, DifferentiableAt ℝ h t := by
    intro t
    have heq : h = fun t => (F (t + δ) - F t) * (F δ)⁻¹ := by
      funext t
      rw [← havg t, mul_assoc, mul_inv_cancel₀ hδ, mul_one]
    rw [heq]
    have hA : DifferentiableAt ℝ (fun t : ℝ => F (t + δ)) t := by
      have := (hF (t + δ)).differentiableAt
      exact this.comp t ((differentiableAt_id).add_const δ)
    exact (hA.sub (hF t).differentiableAt).mul_const _
  set c : ℂ := deriv h 0 with hc_def
  have hderiv : ∀ t, HasDerivAt h (h t * c) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => h (t + u)) (deriv h t) 0 := by
      have hin : HasDerivAt (fun u : ℝ => t + u) (1 : ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add t
      have hout : HasDerivAt h (deriv h (t + 0)) (t + 0) := (hdiff (t + 0)).hasDerivAt
      have h3 := hout.scomp (0 : ℝ) hin
      simp [Function.comp] at h3
      exact h3
    have h4 : HasDerivAt (fun u : ℝ => h t * h u) (h t * c) 0 := by
      have := ((hdiff 0).hasDerivAt).const_mul (h t)
      simpa [hc_def] using this
    have hfun : (fun u : ℝ => h (t + u)) = fun u => h t * h u := funext fun u => hadd t u
    rw [hfun] at h1
    have h5 : deriv h t = h t * c := h1.unique h4
    rw [← h5]
    exact (hdiff t).hasDerivAt
  refine ⟨c, fun t => ?_⟩
  set k : ℝ → ℂ := fun t => h t * Complex.exp (-(c * t)) with hk_def
  have hexp : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * (t : ℂ))))
      (Complex.exp (-(c * (t : ℂ))) * (-c)) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(c * z))) (Complex.exp (-(c * (t : ℂ))) * (-c))
        (t : ℂ) := by
      have h2 : HasDerivAt (fun z : ℂ => -(c * z)) (-c) (t : ℂ) := by
        have h__af := (((hasDerivAt_id (t : ℂ)).const_mul c).neg)
        simp at h__af
        exact h__af
      exact (Complex.hasDerivAt_exp _).comp (t : ℂ) h2
    exact h1.comp_ofReal
  have hk : ∀ t, HasDerivAt k 0 t := by
    intro t
    have := (hderiv t).mul (hexp t)
    simp only [hk_def]
    convert this using 1
    · rfl
    · rfl
    ring
  have hconst : ∀ t, k t = k 0 := by
    intro t
    exact is_const_of_deriv_eq_zero (fun t => (hk t).differentiableAt)
      (fun t => (hk t).deriv) t 0
  have hk0 : k 0 = 1 := by simp [hk_def, h0]
  have hkt : h t * Complex.exp (-(c * t)) = 1 := by
    have := hconst t
    rw [hk0] at this
    simpa [hk_def] using this
  have hne : Complex.exp (-(c * t)) ≠ 0 := Complex.exp_ne_zero _
  calc h t = h t * Complex.exp (-(c * t)) * Complex.exp (c * t) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (c * t) := by rw [hkt, one_mul]

private theorem exists_eq_cpow_of_continuousOn_of_mul {g : ℝ → ℂ} (hg : ContinuousOn g (Set.Ioi 0))
    (hmul : ∀ x y : ℝ, 0 < x → 0 < y → g (x * y) = g x * g y) (hg1 : g 1 ≠ 0) :
    ∃ c : ℂ, ∀ r : ℝ, 0 < r → g r = (r : ℂ) ^ c := by
  set h : ℝ → ℂ := fun t => g (Real.exp t) with hh_def
  have hcont : Continuous h := by
    apply hg.comp_continuous Real.continuous_exp
    intro t; exact Real.exp_pos t
  have hadd : ∀ s t, h (s + t) = h s * h t := by
    intro s t
    simp only [hh_def, Real.exp_add]
    exact hmul _ _ (Real.exp_pos s) (Real.exp_pos t)
  have h0 : h 0 = 1 := by
    have h1 : g 1 = g 1 * g 1 := by simpa using hmul 1 1 one_pos one_pos
    have h2 : g 1 = 1 := by
      have h3 : g 1 * (g 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hg1
      · exact sub_eq_zero.mp h4
    simpa [hh_def] using h2
  obtain ⟨c, hc⟩ := exists_eq_exp_mul_of_continuous_of_add hcont hadd h0
  refine ⟨c, fun r hr => ?_⟩
  have h1 : g r = h (Real.log r) := by
    simp only [hh_def, Real.exp_log hr]
  rw [h1, hc, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le,
    mul_comm]

private theorem exists_forall_rpow_eq_cpow_of_continuousOn_of_mul {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Ioi 0))
    (hmul : ∀ x y : ℝ, 0 < x → 0 < y → g (x * y) = g x * g y) (hg1 : g 1 ≠ 0) :
    ∃ c : ℂ, ∀ b : ℝ, 0 < b → ∀ e : ℝ, g (b ^ e) = (b : ℂ) ^ ((e : ℂ) * c) := by
  obtain ⟨c, hc⟩ := exists_eq_cpow_of_continuousOn_of_mul hg hmul hg1
  refine ⟨c, fun b hb e => ?_⟩
  rw [hc _ (Real.rpow_pos_of_pos hb e)]
  exact (Complex.cpow_mul_ofReal_nonneg hb.le e c).symm

end CpowClassification

namespace WeylFlatContinuation
namespace Local

open scoped Classical in

private theorem continuous_archUnitHom (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    Continuous (fun a : (w.Completion)ˣ => NumberField.TateGlobal.archUnitHom (F := F) w a) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous (fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion), (1 : FiniteAdeleRing (𝓞 F) F)) :
        AdeleRing (𝓞 F) F))
    exact (continuous_const.update w Units.continuous_val).prodMk continuous_const
  · show Continuous (fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w (((a⁻¹ : (w.Completion)ˣ)) : w.Completion),
        (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F))
    exact (continuous_const.update w Units.continuous_coe_inv).prodMk continuous_const

private theorem continuous_char_archUnitHom (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (w : InfinitePlace F) :
    Continuous (fun a : (w.Completion)ˣ =>
      ((χ (NumberField.TateGlobal.archUnitHom (F := F) w a) : ℂˣ) : ℂ)) :=
  Units.continuous_val.comp (hχc.comp (continuous_archUnitHom F w))

private theorem re_eq_zero_of_norm_two_cpow (c : ℂ) (h : ‖((2 : ℝ) : ℂ) ^ c‖ = 1) : c.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos two_pos] at h
  have h' := congrArg Real.log h
  rw [Real.log_rpow two_pos, Real.log_one] at h'
  exact (mul_eq_zero.1 h').resolve_right (Real.log_pos one_lt_two).ne'

private theorem exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isReal (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (i : {w : InfinitePlace F // w.IsReal}) (R : ℝ → ℂ)
    (hR : ∀ u : (i.1.Completion)ˣ,
      0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
      R (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
        = ((χ (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ)) :
    ∃ c : ℂ, c.re = 0 ∧ ∀ b : ℝ, 0 < b → ∀ e : ℝ, R (b ^ e) = (b : ℂ) ^ ((e : ℂ) * c) := by
  have hRu : ∀ (r : ℝ), 0 < r → ∀ u : (i.1.Completion)ˣ,
      Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) = r →
      R r = ((χ (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ) := by
    intro r hr u hu
    have h := hR u (by rw [hu]; exact hr)
    rwa [hu] at h
  let ψ : ℝ → i.1.Completion := (Completion.isometryEquivRealOfIsReal i.2).symm
  have hψ : ∀ r : ℝ, Completion.extensionEmbeddingOfIsReal i.2 (ψ r) = r := fun r =>
    (Completion.isometryEquivRealOfIsReal i.2).apply_symm_apply r
  have hψc : Continuous ψ := (Completion.isometryEquivRealOfIsReal i.2).symm.continuous
  have hψ0 : ∀ r : ℝ, 0 < r → ψ r ≠ 0 := by
    intro r hr h0
    have h := hψ r
    rw [h0, map_zero] at h
    exact hr.ne h
  have hmul : ∀ x y : ℝ, 0 < x → 0 < y → R (x * y) = R x * R y := by
    intro x y hx hy
    rw [hRu x hx (Units.mk0 _ (hψ0 x hx)) (hψ x), hRu y hy (Units.mk0 _ (hψ0 y hy)) (hψ y),
      hRu (x * y) (mul_pos hx hy) (Units.mk0 _ (hψ0 x hx) * Units.mk0 _ (hψ0 y hy))
        (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0, map_mul, hψ, hψ]),
      map_mul, map_mul, Units.val_mul]
  have hone : R 1 ≠ 0 := by
    rw [hRu 1 one_pos 1 (by rw [Units.val_one, map_one])]
    exact Units.ne_zero _
  have hcont : ContinuousOn R (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_restrict]
    let U : Set.Ioi (0 : ℝ) → (i.1.Completion)ˣ := fun r => Units.mk0 (ψ r.1) (hψ0 r.1 r.2)
    have hU : Continuous U := by
      rw [Units.continuous_iff]
      refine ⟨hψc.comp continuous_subtype_val, ?_⟩
      exact (hψc.comp continuous_subtype_val).inv₀ (fun r => hψ0 r.1 r.2)
    refine ((continuous_char_archUnitHom F χ hχc i.1).comp hU).congr ?_
    intro r
    exact (hRu r.1 r.2 (U r) (hψ r.1)).symm
  obtain ⟨c, hc⟩ := CpowClassification.exists_forall_rpow_eq_cpow_of_continuousOn_of_mul hcont hmul hone
  refine ⟨c, ?_, hc⟩
  apply re_eq_zero_of_norm_two_cpow
  have h2 := hc 2 two_pos 1
  rw [Real.rpow_one, Complex.ofReal_one, one_mul] at h2
  rw [← h2, hRu 2 two_pos (Units.mk0 _ (hψ0 2 two_pos)) (hψ 2)]
  exact hχu _

private theorem exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isComplex (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (w : {w : InfinitePlace F // w.IsComplex}) (R : ℝ → ℂ)
    (hR : ∀ (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
      Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
      R r = ((χ (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ)) :
    ∃ c : ℂ, c.re = 0 ∧ ∀ b : ℝ, 0 < b → ∀ e : ℝ, R (b ^ e) = (b : ℂ) ^ ((e : ℂ) * c) := by
  let ψ : ℂ → w.1.Completion := (Completion.isometryEquivComplexOfIsComplex w.2).symm
  have hψ : ∀ z : ℂ, Completion.extensionEmbedding w.1 (ψ z) = z := fun z =>
    (Completion.isometryEquivComplexOfIsComplex w.2).apply_symm_apply z
  have hψc : Continuous ψ := (Completion.isometryEquivComplexOfIsComplex w.2).symm.continuous
  have hψ0 : ∀ r : ℝ, 0 < r → ψ r ≠ 0 := by
    intro r hr h0
    have h := hψ r
    rw [h0, map_zero] at h
    exact hr.ne (by exact_mod_cast h)
  have hmul : ∀ x y : ℝ, 0 < x → 0 < y → R (x * y) = R x * R y := by
    intro x y hx hy
    rw [hR (Units.mk0 _ (hψ0 x hx)) x hx (hψ x), hR (Units.mk0 _ (hψ0 y hy)) y hy (hψ y),
      hR (Units.mk0 _ (hψ0 x hx) * Units.mk0 _ (hψ0 y hy)) (x * y) (mul_pos hx hy)
        (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0, map_mul, hψ, hψ, Complex.ofReal_mul]),
      map_mul, map_mul, Units.val_mul]
  have hone : R 1 ≠ 0 := by
    rw [hR 1 1 one_pos (by rw [Units.val_one, map_one, Complex.ofReal_one])]
    exact Units.ne_zero _
  have hcont : ContinuousOn R (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_restrict]
    let U : Set.Ioi (0 : ℝ) → (w.1.Completion)ˣ := fun r => Units.mk0 (ψ r.1) (hψ0 r.1 r.2)
    have hU : Continuous U := by
      rw [Units.continuous_iff]
      refine ⟨hψc.comp (Complex.continuous_ofReal.comp continuous_subtype_val), ?_⟩
      exact (hψc.comp (Complex.continuous_ofReal.comp continuous_subtype_val)).inv₀
        (fun r => hψ0 r.1 r.2)
    refine ((continuous_char_archUnitHom F χ hχc w.1).comp hU).congr ?_
    intro r
    exact (hR (U r) r.1 r.2 (hψ r.1)).symm
  obtain ⟨c, hc⟩ := CpowClassification.exists_forall_rpow_eq_cpow_of_continuousOn_of_mul hcont hmul hone
  refine ⟨c, ?_, hc⟩
  apply re_eq_zero_of_norm_two_cpow
  have h2 := hc 2 two_pos 1
  rw [Real.rpow_one, Complex.ofReal_one, one_mul] at h2
  rw [← h2, hR (Units.mk0 _ (hψ0 2 two_pos)) 2 two_pos (hψ 2)]
  exact hχu _

private theorem norm_pin_eq_one (R : ℝ → ℂ) (c : ℂ) (hc0 : c.re = 0)
    (hc : ∀ b : ℝ, 0 < b → ∀ e : ℝ, R (b ^ e) = (b : ℂ) ^ ((e : ℂ) * c)) (r : ℝ) (hr : 0 < r) :
    ‖R r‖ = 1 := by
  have h := hc r hr 1
  rw [Real.rpow_one] at h
  rw [h, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    hc0, mul_zero, zero_mul, sub_zero, Real.rpow_zero]

private theorem real_factor_eq (R : ℝ → ℂ) (c : ℂ)
    (hc : ∀ b : ℝ, 0 < b → ∀ e : ℝ, R (b ^ e) = (b : ℂ) ^ ((e : ℂ) * c)) (k : ℤ) (s : ℂ) (y : ℝ) :
    R ((1 + y ^ 2) ^ (-(1 / 2 : ℝ)))
        * (((y : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) ^ k
        * ((1 + y ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (((y : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) ^ k
        * ((1 + y ^ 2 : ℝ) : ℂ) ^ (-((s + ((1 / 2 : ℝ) : ℂ) * c) + 1 / 2)) := by
  have hb : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hb0 : ((1 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hc _ hb, mul_right_comm, ← Complex.cpow_add _ _ hb0, mul_comm]
  congr 2
  push_cast
  ring

private theorem complex_factor_eq (R : ℝ → ℂ) (c : ℂ)
    (hc : ∀ b : ℝ, 0 < b → ∀ e : ℝ, R (b ^ e) = (b : ℂ) ^ ((e : ℂ) * c)) (a b m : ℕ) (s : ℂ) (z : ℂ) :
    R ((1 + ‖z‖ ^ 2) ^ (-(1 / 2 : ℝ))) * z ^ a * (starRingEnd ℂ) z ^ b
        * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1) - (m : ℂ) / 2)
      = z ^ a * (starRingEnd ℂ) z ^ b
        * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) * s + ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * c)) := by
  have hb : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hb0 : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hc _ hb, show ∀ p q r t : ℂ, p * q * r * t = q * r * (p * t) from fun p q r t => by ring,
    ← Complex.cpow_add _ _ hb0]
  congr 2
  push_cast
  ring

private theorem norm_real_unit (y : ℝ) :
    ‖((y : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  rw [norm_div, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    div_eq_one_iff_eq (Real.sqrt_pos.2 hpos).ne', ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm,
    Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

private theorem re_shift (s c : ℂ) (hc0 : c.re = 0) : (s + ((1 / 2 : ℝ) : ℂ) * c).re = s.re := by
  rw [Complex.add_re, Complex.re_ofReal_mul, hc0, mul_zero, add_zero]

private theorem re_param (s c : ℂ) (hc0 : c.re = 0) (m : ℕ) :
    (((2 : ℝ) : ℂ) * s + ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * c).re = 2 * s.re + (1 + (m : ℝ) / 2) := by
  rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re,
    hc0, mul_zero, add_zero]

private theorem integrable_real_factor (k : ℤ) (s : ℂ) (hs : 1 / 2 < s.re) :
    Integrable (fun y : ℝ => (((y : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) ^ k
      * ((1 + y ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))) := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 * s.re + 1 := by
    rw [Module.finrank_self]
    push_cast
    linarith
  have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  refine (integrable_rpow_neg_one_add_norm_sq (μ := volume) hr).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ ?_)
    · refine Continuous.zpow₀ ?_ k (fun y => Or.inl (div_ne_zero ?_ ?_))
      · refine (Complex.continuous_ofReal.sub continuous_const).div
          (Complex.continuous_ofReal.comp
            (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))) (fun y => ?_)
        exact_mod_cast (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + y ^ 2)).ne'
      · intro h
        have h' := congrArg Complex.im h
        simp at h'
      · exact_mod_cast (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + y ^ 2)).ne'
    · exact (Complex.continuous_ofReal.comp (continuous_const.add (continuous_pow 2))).cpow
        continuous_const
        (fun y => Complex.ofReal_mem_slitPlane.2 (by positivity : (0 : ℝ) < 1 + y ^ 2))
  · refine Filter.Eventually.of_forall (fun y => ?_)
    have hb : (0 : ℝ) < 1 + y ^ 2 := by positivity
    rw [norm_mul, norm_zpow, norm_real_unit, one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb,
      Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    congr 1
    rw [Complex.neg_re, Complex.add_re, h12]
    ring

private theorem integrable_complex_factor (a b m : ℕ) (habm : a + b ≤ m) (s : ℂ) (hs : 1 / 2 < s.re)
    (c : ℂ) (hc0 : c.re = 0) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b
      * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) * s + ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * c))) := by
  have hr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < 2 * (2 * s.re + 1) := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  have habm' : (a : ℝ) + b ≤ m := by exact_mod_cast habm
  refine (integrable_rpow_neg_one_add_norm_sq (μ := volume) hr).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable
      (((continuous_id.pow a).mul (Complex.continuous_conj.pow b)).mul ?_)
    exact (Complex.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2))).cpow
      continuous_const
      (fun z => Complex.ofReal_mem_slitPlane.2 (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2))
  · refine Filter.Eventually.of_forall (fun z => ?_)
    have hB : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have hB1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_right (by positivity)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add,
      Complex.norm_cpow_eq_rpow_re_of_pos hB, Complex.neg_re, re_param s c hc0 m]
    have h1 : ‖z‖ ^ (a + b) ≤ (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) := by
      have hz : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ (1 / (2 : ℝ)) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (norm_nonneg _) hB.le]
        linarith
      calc ‖z‖ ^ (a + b) ≤ ((1 + ‖z‖ ^ 2) ^ (1 / (2 : ℝ))) ^ (a + b) :=
            pow_le_pow_left₀ (norm_nonneg _) hz _
        _ = (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
            congr 1
            ring
    calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + (1 + (m : ℝ) / 2)))
        ≤ (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + (1 + (m : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB.le _)
      _ = (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2 + -(2 * s.re + (1 + (m : ℝ) / 2))) :=
          (Real.rpow_add hB _ _).symm
      _ ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le hB1
          push_cast
          linarith

private theorem meromorphicOn_gammaR_comp (L : ℂ → ℂ) (hL : Differentiable ℂ L) :
    MeromorphicOn (fun s => Complex.Gammaℝ (L s)) Set.univ := by
  intro z _
  show MeromorphicAt (fun s => (Real.pi : ℂ) ^ (-(L s) / 2) * Complex.Gamma (L s / 2)) z
  have h1 : MeromorphicAt (fun s => (Real.pi : ℂ) ^ (-(L s) / 2)) z :=
    (((hL.neg.div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))).analyticAt z).meromorphicAt
  have h2 : MeromorphicAt (fun s => Complex.Gamma (L s / 2)) z :=
    MeromorphicAt.comp_analyticAt (g := fun s => L s / 2)
      (MeromorphicOn.Gamma (s := Set.univ) (L z / 2) (Set.mem_univ _)) ((hL.div_const 2).analyticAt z)
  exact h1.mul h2

private theorem meromorphicOn_gamma_comp (L : ℂ → ℂ) (hL : Differentiable ℂ L) :
    MeromorphicOn (fun s => Complex.Gamma (L s)) Set.univ := fun z _ =>
  (MeromorphicOn.Gamma (s := Set.univ) (L z) (Set.mem_univ _)).comp_analyticAt (hL.analyticAt z)

private theorem meromorphicOn_prod {ι : Type} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, MeromorphicOn (f i) Set.univ) : MeromorphicOn (fun s => ∏ i, f i s) Set.univ := by
  have key : MeromorphicOn (∏ i, f i) Set.univ :=
    Finset.prod_induction f (fun g => MeromorphicOn g Set.univ) (fun g h hg hh => hg.mul hh)
      (MeromorphicOn.const 1) (fun i _ => hf i)
  convert key using 1
  funext s
  simp

private theorem meromorphicOn_real_value (k : ℤ) (c : ℂ) :
    MeromorphicOn (fun s : ℂ => (-Complex.I) ^ k
      * (Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * c))
          * Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * c) + 1))
      / (Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * c) + 1 + k)
          * Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * c) + 1 - k))) Set.univ := by
  have hL : Differentiable ℂ (fun s : ℂ => 2 * (s + ((1 / 2 : ℝ) : ℂ) * c)) := by fun_prop
  exact ((MeromorphicOn.const _).mul
      ((meromorphicOn_gammaR_comp _ hL).mul (meromorphicOn_gammaR_comp _ (hL.add_const 1)))).div
    ((meromorphicOn_gammaR_comp _ ((hL.add_const 1).add_const (k : ℂ))).mul
      (meromorphicOn_gammaR_comp _ ((hL.add_const 1).sub_const (k : ℂ))))

private theorem meromorphicOn_complex_value (a b m : ℕ) (c : ℂ) :
    MeromorphicOn (fun s : ℂ => if a = b then
        (Real.pi : ℂ) * (a.factorial : ℂ)
          * Complex.Gamma
              ((((2 : ℝ) : ℂ) * s + ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * c)
                - 1 - a)
          / Complex.Gamma
              (((2 : ℝ) : ℂ) * s + ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * c)
      else 0) Set.univ := by
  by_cases hab : a = b
  · simp only [if_pos hab]
    have hL : Differentiable ℂ (fun s : ℂ =>
        ((2 : ℝ) : ℂ) * s + ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * c) := by
      fun_prop
    exact ((MeromorphicOn.const _).mul
        (meromorphicOn_gamma_comp _ ((hL.sub_const 1).sub_const (a : ℂ)))).div
      (meromorphicOn_gamma_comp _ hL)
  · simp only [if_neg hab]
    exact MeromorphicOn.const 0

open scoped Classical in

private theorem integrand_absorbed
    (F : Type) [Field F] [NumberField F]
    (k : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (cr : {w : InfinitePlace F // w.IsReal} → ℂ) (cc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hcr : ∀ i, ∀ b : ℝ, 0 < b → ∀ e : ℝ, Rr i (b ^ e) = (b : ℂ) ^ ((e : ℂ) * cr i))
    (hcc : ∀ w, ∀ b : ℝ, 0 < b → ∀ e : ℝ, Rc w (b ^ e) = (b : ℂ) ^ ((e : ℂ) * cc w))
    (s : ℂ) (y : mixedEmbedding.mixedSpace F) :
        (∏ i : {w : InfinitePlace F // w.IsReal},
            Rr i ((1 + (y.1 i) ^ 2) ^ (-(1 / 2 : ℝ)))
              * ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (k i)
              * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
            Rc w ((1 + ‖y.2 w‖ ^ 2) ^ (-(1 / 2 : ℝ)))
              * (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
              * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - ((abm w).2.2 : ℂ) / 2))
      = (∏ i : {w : InfinitePlace F // w.IsReal},
            ((((y.1 i : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (y.1 i) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
            (y.2 w) ^ ((abm w).1) * (starRingEnd ℂ) (y.2 w) ^ ((abm w).2.1)
                * ((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w)) := by
  exact congrArg₂ (· * ·)
    (Finset.prod_congr rfl (fun i _ => real_factor_eq (Rr i) (cr i) (hcr i) (k i) s (y.1 i)))
    (Finset.prod_congr rfl (fun w _ =>
      complex_factor_eq (Rc w) (cc w) (hcc w) (abm w).1 (abm w).2.1 (abm w).2.2 s (y.2 w)))

open scoped Classical in

private theorem integrable_absorbed
    (F : Type) [Field F] [NumberField F]
    (k : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2)
    (cr : {w : InfinitePlace F // w.IsReal} → ℂ) (cc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hcc0 : ∀ w, (cc w).re = 0) (hcr0 : ∀ i, (cr i).re = 0) (s : ℂ) (hs : 1 / 2 < s.re) :
    Integrable (fun y : mixedEmbedding.mixedSpace F =>
      (∏ i : {w : InfinitePlace F // w.IsReal},
          ((((y.1 i : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (y.1 i) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)))
      * ∏ w : {w : InfinitePlace F // w.IsComplex},
          (y.2 w) ^ ((abm w).1) * (starRingEnd ℂ) (y.2 w) ^ ((abm w).2.1)
                * ((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w))) := by
  have hsr : ∀ i : {w : InfinitePlace F // w.IsReal}, 1 / 2 < (s + ((1 / 2 : ℝ) : ℂ) * cr i).re := by
    intro i
    rw [re_shift s (cr i) (hcr0 i)]
    exact hs
  have hfr := Integrable.fintype_prod (fun i : {w : InfinitePlace F // w.IsReal} =>
    integrable_real_factor (k i) (s + ((1 / 2 : ℝ) : ℂ) * cr i) (hsr i))
  have hfc := Integrable.fintype_prod (fun w : {w : InfinitePlace F // w.IsComplex} =>
    integrable_complex_factor (abm w).1 (abm w).2.1 (abm w).2.2 (habm w) s hs (cc w) (hcc0 w))
  have hI := Integrable.mul_prod hfr hfc
  exact hI

open scoped Classical in

private theorem integral_absorbed
    (F : Type) [Field F] [NumberField F]
    (k : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2)
    (cr : {w : InfinitePlace F // w.IsReal} → ℂ) (cc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hcc0 : ∀ w, (cc w).re = 0) (hcr0 : ∀ i, (cr i).re = 0) (s : ℂ) (hs : 1 / 2 < s.re) :
    (∫ y : mixedEmbedding.mixedSpace F,
        (∏ i : {w : InfinitePlace F // w.IsReal},
            ((((y.1 i : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (y.1 i) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
            (y.2 w) ^ ((abm w).1) * (starRingEnd ℂ) (y.2 w) ^ ((abm w).2.1)
                * ((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w)))
      = (∏ i : {w : InfinitePlace F // w.IsReal},
        (-Complex.I) ^ (k i)
            * (Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i))
                * Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1))
            / (Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 + k i)
                * Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 - k i)))
      * ∏ w : {w : InfinitePlace F // w.IsComplex},
          (if (abm w).1 = (abm w).2.1 then
              (Real.pi : ℂ) * ((abm w).1).factorial * Complex.Gamma
                ((((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * cc w)
                  - 1 - (abm w).1)
                / Complex.Gamma
                  (((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * cc w)
            else 0) := by
  have hF : ∫ y : mixedEmbedding.mixedSpace F,
      (∏ i : {w : InfinitePlace F // w.IsReal},
          ((((y.1 i : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (y.1 i) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)))
      * ∏ w : {w : InfinitePlace F // w.IsComplex},
          (y.2 w) ^ ((abm w).1) * (starRingEnd ℂ) (y.2 w) ^ ((abm w).2.1)
                * ((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w))
      = (∫ yr : ({w : InfinitePlace F // w.IsReal} → ℝ),
          ∏ i : {w : InfinitePlace F // w.IsReal},
            ((((yr i : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (yr i) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (yr i) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)))
        * ∫ yc : ({w : InfinitePlace F // w.IsComplex} → ℂ),
          ∏ w : {w : InfinitePlace F // w.IsComplex},
            (yc w) ^ ((abm w).1) * (starRingEnd ℂ) (yc w) ^ ((abm w).2.1)
                * ((1 + ‖yc w‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w)) :=
    integral_prod_mul (μ := volume) (ν := volume)
      (fun yr : ({w : InfinitePlace F // w.IsReal} → ℝ) =>
        ∏ i : {w : InfinitePlace F // w.IsReal},
          ((((yr i : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (yr i) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (yr i) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)))
      (fun yc : ({w : InfinitePlace F // w.IsComplex} → ℂ) =>
        ∏ w : {w : InfinitePlace F // w.IsComplex},
          (yc w) ^ ((abm w).1) * (starRingEnd ℂ) (yc w) ^ ((abm w).2.1)
                * ((1 + ‖yc w‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w)))
  have hR : ∫ yr : ({w : InfinitePlace F // w.IsReal} → ℝ),
      ∏ i : {w : InfinitePlace F // w.IsReal},
        ((((yr i : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (yr i) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (yr i) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2))
      = ∏ i : {w : InfinitePlace F // w.IsReal}, ∫ y : ℝ,
        ((((y : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (y) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (y) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)) :=
    integral_fintype_prod_volume_eq_prod (fun (i : {w : InfinitePlace F // w.IsReal}) (y : ℝ) =>
      ((((y : ℝ) : ℂ) - Complex.I)
                  / ((Real.sqrt (1 + (y) ^ 2) : ℝ) : ℂ)) ^ (k i)
                * ((1 + (y) ^ 2 : ℝ) : ℂ)
                  ^ (-((s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 / 2)))
  have hC : ∫ yc : ({w : InfinitePlace F // w.IsComplex} → ℂ),
      ∏ w : {w : InfinitePlace F // w.IsComplex},
        (yc w) ^ ((abm w).1) * (starRingEnd ℂ) (yc w) ^ ((abm w).2.1)
                * ((1 + ‖yc w‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w))
      = ∏ w : {w : InfinitePlace F // w.IsComplex}, ∫ z : ℂ,
        (z) ^ ((abm w).1) * (starRingEnd ℂ) (z) ^ ((abm w).2.1)
                * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w)) :=
    integral_fintype_prod_volume_eq_prod (fun (w : {w : InfinitePlace F // w.IsComplex}) (z : ℂ) =>
      (z) ^ ((abm w).1) * (starRingEnd ℂ) (z) ^ ((abm w).2.1)
                * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)
                  ^ (-(((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ)
                    + ((1 / 2 : ℝ) : ℂ) * cc w)))
  have hsr' : ∀ i : {w : InfinitePlace F // w.IsReal}, 0 < (s + ((1 / 2 : ℝ) : ℂ) * cr i).re := by
    intro i
    rw [re_shift s (cr i) (hcr0 i)]
    linarith
  have hsc : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (((abm w).1 : ℝ) + (abm w).2.1) / 2 + 1
        < (((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * cc w).re := by
    intro w
    rw [re_param s (cc w) (hcc0 w) (abm w).2.2]
    have h' : ((abm w).1 : ℝ) + (abm w).2.1 ≤ (abm w).2.2 := by exact_mod_cast habm w
    linarith
  rw [hF, hR, hC]
  exact congrArg₂ (· * ·)
    (Finset.prod_congr rfl (fun i _ =>
      AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
        (k i) (s + ((1 / 2 : ℝ) : ℂ) * cr i) (hsr' i)))
    (Finset.prod_congr rfl (fun w _ =>
      AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
        (abm w).1 (abm w).2.1
        (((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * cc w)
        (hsc w)))

open scoped Classical in
private theorem archFactor_meromorphic (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hχc : Continuous (μ * ν⁻¹))
    (k : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (hRr : ∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
      0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
      Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
        = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ))
    (hRc : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
      Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
      Rc w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ)) :
    ∃ Ma : ℂ → ℂ, MeromorphicOn Ma Set.univ ∧ ∀ s : ℂ, 1 / 2 < s.re →
      Integrable (fun y : mixedEmbedding.mixedSpace F =>
        (∏ i : {w : InfinitePlace F // w.IsReal},
            Rr i ((1 + (y.1 i) ^ 2) ^ (-(1 / 2 : ℝ)))
              * ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (k i)
              * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
            Rc w ((1 + ‖y.2 w‖ ^ 2) ^ (-(1 / 2 : ℝ)))
              * (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
              * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - ((abm w).2.2 : ℂ) / 2))) ∧
      Ma s = ∫ y : mixedEmbedding.mixedSpace F,
        (∏ i : {w : InfinitePlace F // w.IsReal},
            Rr i ((1 + (y.1 i) ^ 2) ^ (-(1 / 2 : ℝ)))
              * ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (k i)
              * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
            Rc w ((1 + ‖y.2 w‖ ^ 2) ^ (-(1 / 2 : ℝ)))
              * (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
              * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - ((abm w).2.2 : ℂ) / 2)) := by
  have hχu : ∀ x, ‖(((μ * ν⁻¹) x : ℂˣ) : ℂ)‖ = 1 := by
    intro x
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, hμ x, hν x, inv_one, mul_one]
  choose cr hcr using fun i : {w : InfinitePlace F // w.IsReal} =>
    exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isReal F (μ * ν⁻¹) hχc hχu i (Rr i) (hRr i)
  choose cc hcc using fun w : {w : InfinitePlace F // w.IsComplex} =>
    exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isComplex F (μ * ν⁻¹) hχc hχu w (Rc w) (hRc w)
  refine ⟨fun s : ℂ =>
    (∏ i : {w : InfinitePlace F // w.IsReal},
        (-Complex.I) ^ (k i)
            * (Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i))
                * Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1))
            / (Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 + k i)
                * Complex.Gammaℝ (2 * (s + ((1 / 2 : ℝ) : ℂ) * cr i) + 1 - k i)))
      * ∏ w : {w : InfinitePlace F // w.IsComplex},
          (if (abm w).1 = (abm w).2.1 then
              (Real.pi : ℂ) * ((abm w).1).factorial * Complex.Gamma
                ((((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * cc w)
                  - 1 - (abm w).1)
                / Complex.Gamma
                  (((2 : ℝ) : ℂ) * s + ((1 + ((abm w).2.2 : ℝ) / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * cc w)
            else 0), ?_, ?_⟩
  · exact (meromorphicOn_prod _ (fun i => meromorphicOn_real_value (k i) (cr i))).mul
      (meromorphicOn_prod _
        (fun w => meromorphicOn_complex_value (abm w).1 (abm w).2.1 (abm w).2.2 (cc w)))
  intro s hs
  have hint := integrand_absorbed F k abm Rr Rc cr cc (fun i => (hcr i).2) (fun w => (hcc w).2) s
  refine ⟨(integrable_absorbed F k abm habm cr cc (fun w => (hcc w).1) (fun i => (hcr i).1) s hs).congr
    (Filter.Eventually.of_forall (fun y => (hint y).symm)), ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hint)]
  exact (integral_absorbed F k abm habm cr cc (fun w => (hcc w).1) (fun i => (hcr i).1) s hs).symm

end WeylFlatContinuation.Local

namespace WeylFlatContinuation
namespace Local

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

private noncomputable def pureTensorTerm
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
      (∏ i : {w : InfinitePlace F // w.IsReal},
          Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) ^ (-(1 / 2 : ℝ)))
            * ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ) - Complex.I)
                / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                    : ℝ) : ℂ)) ^ (kdat j i)
            * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ))
                ^ (-(s + 1 / 2)))
      * (∏ w : {w : InfinitePlace F // w.IsComplex},
          Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2) ^ (-(1 / 2 : ℝ)))
            * Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm j w).1
            * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1)) ^ (abm j w).2.1
            * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
                ^ (-(2 * s + 1) - ((abm j w).2.2 : ℂ) / 2))
      * (∏ v ∈ S,
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) (x.2 v)
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt
                    (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                  * B j v y⁻¹) (x.2 v)))
      * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
              (fun _ => (1 : ℂ)) (x.2 v.1)
            + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt
                    (NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1)⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                (x.2 v.1))

private theorem valued_algebraMap_completion (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) = v.intValuation r := by
  rw [show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) =
      ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

private theorem ball_mem_nhds_completion (v : HeightOneSpectrum (𝓞 F)) (x t : v.adicCompletion F)
    (ht : t ≠ 0) : {z : v.adicCompletion F | Valued.v (z - x) < Valued.v t} ∈ nhds x := by
  have ht' : Valued.v.restrict t ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff, Valuation.zero_iff]
  refine Valued.mem_nhds.mpr ⟨Units.mk0 _ ht', fun z hz => ?_⟩
  rw [Units.val_mk0] at hz
  exact Valued.v.restrict_lt_iff.mp hz

private theorem exists_valued_eq_exp_neg_completion (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ Valued.v t = WithZero.exp (-(N : ℤ)) ∧ Valued.v t ≤ 1 := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (π ^ N)))
      = WithZero.exp (-(N : ℤ)) := by
    rw [valued_algebraMap_completion F v, map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  refine ⟨_, fun h0 => ?_, hv, ?_⟩
  · rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · rw [valued_algebraMap_completion F v]
    exact v.intValuation_le_one _

private theorem levelBall_mem_nhds (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (y₀ : v.adicCompletion F) :
    {z : v.adicCompletion F | Valued.v (z - y₀) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (z - y₀) ≤ 1}
      ∈ nhds y₀ := by
  obtain ⟨t, ht0, hvt, hvt1⟩ := exists_valued_eq_exp_neg_completion F v N
  refine Filter.mem_of_superset (ball_mem_nhds_completion F v y₀ t ht0) fun z hz => ?_
  have hz' : Valued.v (z - y₀) < Valued.v t := hz
  exact ⟨(hz'.trans_eq hvt).le, (hz'.trans_le hvt1).le⟩

private theorem continuous_of_level (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletion F → ℂ) (N : ℕ)
    (hb : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(N : ℤ)) → b y = b x) : Continuous b := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  have hev : Filter.Eventually (fun z => b z = b y₀) (nhds y₀) :=
    Filter.eventually_of_mem (levelBall_mem_nhds F v N y₀) fun z hz => hb y₀ z hz.1
  exact Filter.EventuallyEq.continuousAt hev

private theorem continuousOn_of_level (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F → ℂ) (N : ℕ)
    (ha : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(N : ℤ)) → a y = a x) :
    ContinuousOn a (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro y₀ hy₀
  refine continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
  refine Filter.eventually_of_mem (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (levelBall_mem_nhds F v N y₀))
    self_mem_nhdsWithin) fun z hz => ?_
  exact ha y₀ hy₀ z hz.2 hz.1.1

private theorem continuousOn_charExt (v : HeightOneSpectrum (𝓞 F)) (ψ : (v.adicCompletion F)ˣ →* ℂˣ) (N : ℕ)
    (hψ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v N, ψ u = 1) :
    ContinuousOn (fun y : v.adicCompletion F => LanglandsTunnell.TateLocal.charExt ψ y) {0}ᶜ := by
  intro y₀ hy₀
  have hy0 : y₀ ≠ 0 := Set.mem_compl_singleton_iff.1 hy₀
  suffices hev : Filter.Eventually (fun z => LanglandsTunnell.TateLocal.charExt ψ z
      = LanglandsTunnell.TateLocal.charExt ψ y₀) (nhds y₀) from
    (Filter.EventuallyEq.continuousAt hev).continuousWithinAt
  obtain ⟨t, ht0, hvt, hvt1⟩ := exists_valued_eq_exp_neg_completion F v N
  refine Filter.eventually_of_mem (ball_mem_nhds_completion F v y₀ (t * y₀) (mul_ne_zero ht0 hy0)) fun z hz => ?_
  have hz' : Valued.v (z - y₀) < Valued.v t * Valued.v y₀ := by
    have h : Valued.v (z - y₀) < Valued.v (t * y₀) := hz
    rwa [map_mul] at h
  have hvy0 : Valued.v y₀ ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hlt : Valued.v (z - y₀) < Valued.v y₀ := hz'.trans_le (mul_le_of_le_one_left' hvt1)
  have hvz : Valued.v z = Valued.v y₀ := by
    have h := Valued.v.map_add_eq_of_lt_right hlt
    rwa [sub_add_cancel] at h
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvz
    exact hvy0 hvz.symm
  set u : (v.adicCompletion F)ˣ := Units.mk0 z hz0 * (Units.mk0 y₀ hy0)⁻¹ with hu_def
  have hu : (u : v.adicCompletion F) = z * y₀⁻¹ := by
    simp [hu_def]
  have hu_mem : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v N := by
    rw [LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff]
    refine ⟨?_, Or.inr ?_⟩
    · rw [hu, map_mul, Valuation.map_inv, hvz, mul_inv_cancel₀ hvy0]
    · have h1 : (u : v.adicCompletion F) - 1 = (z - y₀) * y₀⁻¹ := by
        rw [hu, sub_mul, mul_inv_cancel₀ hy0]
      rw [h1, map_mul, Valuation.map_inv, ← hvt]
      exact (mul_inv_lt_of_lt_mul₀ hz').le
  have hmk : Units.mk0 z hz0 = Units.mk0 y₀ hy0 * u := by
    ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, hu, mul_left_comm, mul_inv_cancel₀ hy0, mul_one]
  show LanglandsTunnell.TateLocal.charExt ψ z = LanglandsTunnell.TateLocal.charExt ψ y₀
  rw [LanglandsTunnell.TateLocal.charExt_of_ne_zero ψ hz0, LanglandsTunnell.TateLocal.charExt_of_ne_zero ψ hy0,
    hmk, map_mul, hψ u hu_mem, mul_one]

private theorem continuousOn_modulus_cpow (v : HeightOneSpectrum (𝓞 F)) (c : ℂ) :
    ContinuousOn (fun y : v.adicCompletion F => ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ c) {0}ᶜ := by
  have h : ContinuousOn (fun y : v.adicCompletion F => ((‖y‖ : ℝ) : ℂ) ^ c) {0}ᶜ :=
    ContinuousOn.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousOn continuousOn_const
      fun y hy => Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 (Set.mem_compl_singleton_iff.1 hy))
  refine h.congr fun y _ => ?_
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v y, coe_nnnorm]

private theorem continuous_integers_indicator_add (v : HeightOneSpectrum (𝓞 F))
    {f g : v.adicCompletion F → ℂ} (hf : ContinuousOn f (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (hg : ContinuousOn g (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ) :
    Continuous fun y => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator f y +
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator g y := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := Valued.isOpen_valuationSubring _
  have hC : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isClosed_valuationSubring _
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  by_cases hy : y₀ ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · refine (hf.continuousAt (hO.mem_nhds hy)).congr ?_
    refine Filter.eventually_of_mem (hO.mem_nhds hy) fun y hy' => ?_
    have hy2 : y ∈ v.adicCompletionIntegers F := hy'
    simp [hy2]
  · refine (hg.continuousAt (hC.isOpen_compl.mem_nhds hy)).congr ?_
    refine Filter.eventually_of_mem (hC.isOpen_compl.mem_nhds hy) fun y hy' => ?_
    have hy2 : y ∉ v.adicCompletionIntegers F := hy'
    simp [hy2]

private theorem compl_integers_subset (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ ⊆ ({0}ᶜ : Set (v.adicCompletion F)) := by
  intro y hy
  refine Set.mem_compl_singleton_iff.2 fun h0 => hy ?_
  rw [h0]
  exact (v.adicCompletionIntegers F).zero_mem

private theorem continuous_sFactor (v : HeightOneSpectrum (𝓞 F)) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (N : ℕ)
    (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v N, χ u = 1) (a b : v.adicCompletion F → ℂ) (m : ℕ)
    (ha : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → a y = a x)
    (hb : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → b y = b x) (s : ℂ) :
    Continuous fun y => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator a y +
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * b y⁻¹) y := by
  have hχ' : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v N, χ⁻¹ u = 1 := fun u hu => by
    rw [MonoidHom.inv_apply, hχ u hu, inv_one]
  refine continuous_integers_indicator_add F v (continuousOn_of_level F v a m ha)
    (ContinuousOn.mono ?_ (compl_integers_subset F v))
  exact ((continuousOn_charExt F v χ⁻¹ N hχ').mul (continuousOn_modulus_cpow F v (-(2 * s + 1)))).mul
    ((continuous_of_level F v b m hb).comp_continuousOn continuousOn_inv₀)

private theorem continuous_unrFactor (v : HeightOneSpectrum (𝓞 F)) (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1) (s : ℂ) :
    Continuous fun y => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y +
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y := by
  have hχ' : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v 0, χ⁻¹ u = 1 := fun u hu => by
    rw [MonoidHom.inv_apply, hχ u ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_zero_iff F v).1 hu), inv_one]
  refine continuous_integers_indicator_add F v continuousOn_const (ContinuousOn.mono ?_ (compl_integers_subset F v))
  exact (continuousOn_charExt F v χ⁻¹ 0 hχ').mul (continuousOn_modulus_cpow F v (-(2 * s + 1)))

private theorem continuous_evalFinite (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun x : AdeleRing (𝓞 F) F => x.2 v :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

private theorem continuous_pin_comp (R : ℝ → ℂ) (hR : ContinuousOn R (Set.Ioi 0))
    (e : AdeleRing (𝓞 F) F → ℝ) (he : Continuous e) :
    Continuous fun x => R ((1 + e x ^ 2) ^ (-(1 / 2 : ℝ))) := by
  refine hR.comp_continuous ((continuous_const.add (he.pow 2)).rpow_const fun x => Or.inl ?_) fun x => ?_
  · exact (by positivity : (1 : ℝ) + e x ^ 2 ≠ 0)
  · exact Set.mem_Ioi.2 (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + e x ^ 2) _)

private theorem continuous_ofReal_one_add_sq_cpow (e : AdeleRing (𝓞 F) F → ℝ) (he : Continuous e) (c : ℂ) :
    Continuous fun x => (((1 + e x ^ 2 : ℝ) : ℂ)) ^ c :=
  Continuous.cpow (Complex.continuous_ofReal.comp (continuous_const.add (he.pow 2))) continuous_const
    fun x => Complex.ofReal_mem_slitPlane.2 (by positivity : (0 : ℝ) < 1 + e x ^ 2)

private theorem continuous_realAtom (e : AdeleRing (𝓞 F) F → ℝ) (he : Continuous e) (k : ℤ) :
    Continuous fun x => ((((e x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + e x ^ 2) : ℝ) : ℂ)) ^ k := by
  refine Continuous.zpow₀ ?_ k fun x => Or.inl (div_ne_zero ?_ ?_)
  · exact ((Complex.continuous_ofReal.comp he).sub continuous_const).div₀
      (Complex.continuous_ofReal.comp (continuous_const.add (he.pow 2)).sqrt)
      fun x => Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < 1 + e x ^ 2))
  · intro h
    have him := congrArg Complex.im h
    simp at him
  · exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < 1 + e x ^ 2))

private theorem continuous_embReal (i : {w : InfinitePlace F // w.IsReal}) :
    Continuous fun x : AdeleRing (𝓞 F) F => Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) :=
  (Completion.isometry_extensionEmbeddingOfIsReal i.2).continuous.comp ((continuous_apply i.1).comp continuous_fst)

private theorem continuous_embComplex (w : {w : InfinitePlace F // w.IsComplex}) :
    Continuous fun x : AdeleRing (𝓞 F) F => Completion.extensionEmbedding w.1 (x.1 w.1) :=
  (Completion.isometry_extensionEmbedding w.1).continuous.comp ((continuous_apply w.1).comp continuous_fst)

private theorem continuous_finprod_places (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (hφ : ∀ v, v ∉ S → Continuous (φ v))
    (hφ1 : ∀ v, v ∉ S → ∀ y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)), φ v y = 1) :
    Continuous fun x : AdeleRing (𝓞 F) F => ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, φ v.1 (x.2 v.1) := by
  refine continuous_finprod (fun v => (hφ v.1 v.2).comp (continuous_evalFinite F v.1)) fun x₀ => ?_
  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      ¬ x₀.2.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))}.Finite :=
    Filter.eventually_cofinite.1 x₀.2.2
  have hopen : IsOpen {f : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (¬ x₀.2.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
        f.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have hU : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (¬ x₀.2.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
        x.2.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} := hopen.preimage continuous_snd
  refine ⟨_, hU.mem_nhds fun v hv => not_not.1 hv, ?_⟩
  refine (hfin.preimage (Subtype.val_injective (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ S)).injOn).subset
    fun v hv => ?_
  obtain ⟨x, hxs, hxU⟩ := hv
  intro hvT
  exact hxs (hφ1 v.1 v.2 _ (hxU v.1 (not_not.2 hvT)))

private theorem continuous_pureTensorTerm
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (hRr : ∀ i, ContinuousOn (Rr i) (Set.Ioi 0)) (hRc : ∀ w, ContinuousOn (Rc w) (Set.Ioi 0))
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
      ∀ y ∈ v.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x)
    (hunr : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (hcond : ∀ v ∈ S, ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (j : Fin n) (s : ℂ) : Continuous (pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s) := by
  unfold pureTensorTerm
  refine Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) ?_
  · refine continuous_finsetProd _ fun i _ => ?_
    exact ((continuous_pin_comp F (Rr i) (hRr i) _ (continuous_embReal F i)).mul
      (continuous_realAtom F _ (continuous_embReal F i) (kdat j i))).mul
      (continuous_ofReal_one_add_sq_cpow F _ (continuous_embReal F i) _)
  · refine continuous_finsetProd _ fun w _ => ?_
    exact (((continuous_pin_comp F (Rc w) (hRc w) _ (continuous_embComplex F w).norm).mul
      ((continuous_embComplex F w).pow _)).mul
      ((Complex.continuous_conj.comp (continuous_embComplex F w)).pow _)).mul
      (continuous_ofReal_one_add_sq_cpow F _ (continuous_embComplex F w).norm _)
  · refine continuous_finsetProd _ fun v hv => ?_
    obtain ⟨cN, hcN⟩ := hcond v hv
    exact (continuous_sFactor F v _ cN hcN (A j v) (B j v) m (hA j v hv) (hB j v hv) s).comp
      (continuous_evalFinite F v)
  · refine continuous_finprod_places F S
      (fun w y => (w.adicCompletionIntegers F : Set (w.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y +
        (w.adicCompletionIntegers F : Set (w.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) w)⁻¹ y
            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y)
      (fun w hw => ?_) (fun w _ y hy => ?_)
    · exact continuous_unrFactor F w _ (hunr w hw) s
    · have hy2 : y ∈ w.adicCompletionIntegers F := hy
      simp [hy2]

private theorem aestronglyMeasurable_pureTensorTerm
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (hRr : ∀ i, ContinuousOn (Rr i) (Set.Ioi 0)) (hRc : ∀ w, ContinuousOn (Rc w) (Set.Ioi 0))
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
      ∀ y ∈ v.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x)
    (hunr : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (hcond : ∀ v ∈ S, ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (j : Fin n) (s : ℂ) :
    letI := adeleBorel (𝓞 F) F
    AEStronglyMeasurable (pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s) (adelicAddHaar (𝓞 F) F) := by
  letI := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  exact (continuous_pureTensorTerm F μ ν S n kdat abm m A B Rr Rc hRr hRc hA hB hunr hcond j s).aestronglyMeasurable

section LocalHeights

variable {K : Type*} [NormedField K]

open NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in

private theorem finLocalHeight_of_row (g : GL (Fin 2) K) {x : K}
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = x)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1) :
    finLocalHeight g = ((max 1 ‖x‖)⁻¹) ^ 2 := by
  unfold finLocalHeight rowMaxNorm
  rw [hdet, h10, h11, norm_one, inv_pow, one_div]

open NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in

private theorem localHeight_of_row (g : GL (Fin 2) K) {x : K}
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = x)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1) :
    localHeight g = (1 + ‖x‖ ^ 2)⁻¹ := by
  unfold localHeight rowNormSq
  rw [hdet, h10, h11, norm_one, one_pow, one_div]

end LocalHeights

open NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in

private theorem weyl_inv_mul_unipotent_val (x : AdeleRing (𝓞 F) F) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, x] := by
  have hw : ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, 0] := by
    ext i j
    rw [show adelicWeyl (𝓞 F) F = globalPoints (𝓞 F) F gl2Weyl from rfl, globalPoints_apply, gl2Weyl_val]
    fin_cases i <;> fin_cases j <;> simp
  rw [show (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F from by
      rw [show adelicWeyl (𝓞 F) F = globalPoints (𝓞 F) F gl2Weyl from rfl, ← map_inv, gl2Weyl_inv],
    Units.val_mul, hw, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

open NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in

private theorem adelicHeight_weyl_unipotent (x : AdeleRing (𝓞 F) F) :
    adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
      = (∏ w : InfinitePlace F, ((1 + ‖x.1 w‖ ^ 2)⁻¹) ^ w.mult)
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((max 1 ‖x.2 v‖)⁻¹) ^ 2 := by
  set g : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x with hg
  have hval := weyl_inv_mul_unipotent_val F x
  rw [← hg] at hval
  have h10 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 1 := by
    rw [hval]; rfl
  have h11 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = x := by
    rw [hval]; rfl
  have h00 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = 0 := by
    rw [hval]; rfl
  have h01 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 1 := by
    rw [hval]; rfl

  have harch : ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) = (1 + ‖x.1 w‖ ^ 2)⁻¹ := by
    intro w
    refine localHeight_of_row _ ?_ ?_ ?_
    · rw [archComponent_apply, glArch_apply, h10]; rfl
    · rw [archComponent_apply, glArch_apply, h11]
    · rw [Matrix.det_fin_two, archComponent_apply, archComponent_apply, archComponent_apply,
        archComponent_apply, glArch_apply, glArch_apply, glArch_apply, glArch_apply, h00, h01, h10, h11]
      show ‖(0 : w.Completion) * x.1 w - 1 * 1‖ = 1
      rw [zero_mul, mul_one, zero_sub, norm_neg, norm_one]

  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)) = ((max 1 ‖x.2 v‖)⁻¹) ^ 2 := by
    intro v
    refine finLocalHeight_of_row _ ?_ ?_ ?_
    · rw [finComponent_apply, glFin_apply, h10]; rfl
    · rw [finComponent_apply, glFin_apply, h11]
    · rw [Matrix.det_fin_two, finComponent_apply, finComponent_apply, finComponent_apply,
        finComponent_apply, glFin_apply, glFin_apply, glFin_apply, glFin_apply, h00, h01, h10, h11]
      show ‖(0 : v.adicCompletion F) * x.2 v - 1 * 1‖ = 1
      rw [zero_mul, mul_one, zero_sub, norm_neg, norm_one]
  unfold adelicHeight archHeight finHeight
  rw [Finset.prod_congr rfl fun w _ => by rw [harch w], finprod_congr hfin]

private theorem continuous_heightSection (s : ℂ) :
    Continuous
      (fun g : AdelicGL2 (𝓞 F) F => ((AdelicHeight.adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)) := by
  refine Continuous.cpow (Complex.continuous_ofReal.comp (AdelicHeight.continuous_adelicHeight F))
    continuous_const (fun g => ?_)
  exact Complex.ofReal_mem_slitPlane.2 (AdelicHeight.adelicHeight_pos g)

private theorem norm_heightSection (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    ‖((AdelicHeight.adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)‖
      = AdelicHeight.adelicHeight F g ^ (s.re + 1 / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (AdelicHeight.adelicHeight_pos g), Complex.add_re]
  norm_num

open NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in

private theorem norm_heightSection_weyl_unipotent (s : ℂ) (x : AdeleRing (𝓞 F) F) :
    ‖((adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * 1) : ℝ) : ℂ) ^ (s + 1 / 2)‖
      = ((∏ w : InfinitePlace F, ((1 + ‖x.1 w‖ ^ 2)⁻¹) ^ w.mult)
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((max 1 ‖x.2 v‖)⁻¹) ^ 2) ^ (s.re + 1 / 2) := by
  rw [norm_heightSection, mul_one, adelicHeight_weyl_unipotent]

variable {F} in
omit [NumberField F] in
private theorem norm_embReal {w : InfinitePlace F} (hw : w.IsReal) (y : w.Completion) :
    ‖Completion.extensionEmbeddingOfIsReal hw y‖ = ‖y‖ :=
  (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) y

variable {F} in
omit [NumberField F] in
private theorem sq_embReal {w : InfinitePlace F} (hw : w.IsReal) (y : w.Completion) :
    Completion.extensionEmbeddingOfIsReal hw y ^ 2 = ‖y‖ ^ 2 := by
  rw [← sq_abs, ← Real.norm_eq_abs, norm_embReal]

variable {F} in
omit [NumberField F] in
private theorem norm_embComplex (w : InfinitePlace F) (y : w.Completion) :
    ‖Completion.extensionEmbedding w y‖ = ‖y‖ :=
  (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y

private theorem re_realExp (s : ℂ) : (-(s + 1 / 2)).re = -(s.re + 1 / 2) := by
  simp [Complex.add_re]

private theorem re_complexExp (s : ℂ) (mm : ℕ) :
    (-(2 * s + 1) - (mm : ℂ) / 2).re = -(2 * s.re + 1) - (mm : ℝ) / 2 := by
  simp [Complex.sub_re, Complex.add_re, Complex.mul_re]

private theorem re_finExp (s : ℂ) : (-(2 * s + 1)).re = -(2 * s.re + 1) := by
  simp [Complex.add_re, Complex.mul_re]

private theorem inv_rpow_eq (N : ℝ) (hN : 0 < N) (σ : ℝ) : N⁻¹ ^ (σ + 1 / 2) = N ^ (-(σ + 1 / 2)) := by
  rw [Real.inv_rpow hN.le, Real.rpow_neg hN.le]

private theorem inv_sq_rpow_eq (N : ℝ) (hN : 0 < N) (σ : ℝ) :
    (N⁻¹ ^ 2) ^ (σ + 1 / 2) = N ^ (-(2 * σ + 1)) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (inv_nonneg.mpr hN.le), Real.inv_rpow hN.le,
    ← Real.rpow_neg hN.le]
  congr 1
  ring

private theorem norm_realFactor (R : ℝ → ℂ) (hR : ∀ r : ℝ, 0 < r → ‖R r‖ = 1) (t : ℝ) (k : ℤ)
    (s : ℂ) :
    ‖R ((1 + t ^ 2) ^ (-(1 / 2 : ℝ))) * ((((t : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + t ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))‖
      = (1 + t ^ 2)⁻¹ ^ (s.re + 1 / 2) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hatom : ‖(((t : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im,
      Complex.ofReal_im, Complex.I_im, zero_sub, mul_neg, neg_neg, mul_one]
    rw [div_eq_one_iff_eq (Real.sqrt_ne_zero'.mpr hpos)]
    congr 1
    ring
  rw [norm_mul, norm_mul, hR _ (Real.rpow_pos_of_pos hpos _), norm_zpow, hatom, one_zpow, one_mul,
    one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, re_realExp, inv_rpow_eq _ hpos]

private theorem norm_complexFactor_le (R : ℝ → ℂ) (hR : ∀ r : ℝ, 0 < r → ‖R r‖ = 1) (z : ℂ)
    (a b mm : ℕ) (hab : a + b ≤ mm) (s : ℂ) :
    ‖R ((1 + ‖z‖ ^ 2) ^ (-(1 / 2 : ℝ))) * z ^ a * (starRingEnd ℂ) z ^ b
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - (mm : ℂ) / 2)‖
      ≤ ((1 + ‖z‖ ^ 2)⁻¹ ^ 2) ^ (s.re + 1 / 2) := by
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hone : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  rw [norm_mul, norm_mul, norm_mul, hR _ (Real.rpow_pos_of_pos hpos _), one_mul, norm_pow, norm_pow,
    Complex.norm_conj, ← pow_add, Complex.norm_cpow_eq_rpow_re_of_pos hpos, re_complexExp,
    inv_sq_rpow_eq _ hpos]
  have hmono : ‖z‖ ^ (a + b) ≤ (1 + ‖z‖ ^ 2) ^ ((mm : ℝ) / 2) := by
    have h1 : ‖z‖ ^ (a + b) = (‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
      congr 1
      push_cast
      ring
    rw [h1]
    calc (‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2)
        ≤ (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ (1 + ‖z‖ ^ 2) ^ ((mm : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hone (by
            have : ((a + b : ℕ) : ℝ) ≤ mm := by exact_mod_cast hab
            linarith)
  calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1) - (mm : ℝ) / 2)
      ≤ (1 + ‖z‖ ^ 2) ^ ((mm : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1) - (mm : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hpos.le _)
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1)) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring

variable {F} in
private theorem mem_integers_iff_norm_le_one (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    y ∈ v.adicCompletionIntegers F ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

variable {F} in

private theorem exists_bound_of_level (v : HeightOneSpectrum (𝓞 F)) (G : v.adicCompletion F → ℂ)
    (mm : ℕ)
    (hG : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mm : ℤ)) → G y = G x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ v.adicCompletionIntegers F, ‖G y‖ ≤ C := by
  obtain ⟨t, ht0, hvt⟩ := NumberField.AdelicLevel.exists_valued_eq_exp_neg (K := F) v mm
  have hcpt : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F v)
  have hcont : ContinuousOn G (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro x hx
    have hU : IsOpen {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v t} :=
      (NumberField.AdelicLevel.isOpen_setOf_valued_le v t ht0).preimage (continuous_id.sub continuous_const)
    have hxU : x ∈ {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v t} := by
      simp only [Set.mem_setOf_eq, sub_self, map_zero]
      exact zero_le'
    refine (continuousWithinAt_const (b := G x)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hxU)] with y hy hyU
    exact hG x hx y hy (by simpa [hvt, WithZero.exp] using hyU)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩

private theorem norm_charExt_le_one {K : Type} [Field K] (χ : Kˣ →* ℂˣ)
    (hχ : ∀ u : Kˣ, ‖((χ u : ℂˣ) : ℂ)‖ = 1) (y : K) :
    ‖LanglandsTunnell.TateLocal.charExt χ y‖ ≤ 1 := by
  by_cases hy : y = 0
  · subst hy
    rw [LanglandsTunnell.TateLocal.charExt_zero, norm_zero]
    exact zero_le_one
  · rw [LanglandsTunnell.TateLocal.charExt_of_ne_zero χ hy, hχ]

variable {F} in

private theorem norm_localChar_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    ‖(((NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ u : ℂˣ) : ℂ)‖ = 1 := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, NumberField.TateGlobal.localChar_apply,
    MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
    norm_inv, hμ _, hν _, inv_one, mul_one, inv_one]

variable {F} in

private theorem norm_modulusAtom (v : HeightOneSpectrum (𝓞 F)) {y : v.adicCompletion F} (hy : y ≠ 0)
    (s : ℂ) :
    ‖((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))‖ = ‖y‖ ^ (-(2 * s.re + 1)) := by
  have hmod : (LanglandsTunnell.TateLocal.modulus y : ℝ) = ‖y‖ := by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v y, coe_nnnorm]
  have hpos : (0 : ℝ) < LanglandsTunnell.TateLocal.modulus y := by
    rw [hmod]; exact norm_pos_iff.mpr hy
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, re_finExp, hmod]

variable {F} in

private theorem norm_sFactor_le (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (v : HeightOneSpectrum (𝓞 F))
    (A B : v.adicCompletion F → ℂ) (mm : ℕ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mm : ℤ)) → A y = A x)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mm : ℤ)) → B y = B x) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : v.adicCompletion F,
      ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A y
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt
                  (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                * B y⁻¹) y‖
        ≤ C * ((max 1 ‖y‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_bound_of_level v A mm hA
  obtain ⟨CB, hCB0, hCB⟩ := exists_bound_of_level v B mm (fun x _ y _ h => hB x y h)
  refine ⟨max CA CB, le_max_of_le_left hCA0, fun y => ?_⟩
  by_cases hy : y ∈ v.adicCompletionIntegers F
  · have hy' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_notMem
      (fun h => (show y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) from h) hy'), add_zero]
    have hmax : max 1 ‖y‖ = 1 := max_eq_left ((mem_integers_iff_norm_le_one v y).1 hy)
    rw [hmax, inv_one, one_pow, Real.one_rpow, mul_one]
    exact (hCA y hy).trans (le_max_left _ _)
  · have hy' : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
    rw [Set.indicator_of_notMem hy',
      Set.indicator_of_mem (show y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ from hy'),
      zero_add]
    have hlt : 1 < ‖y‖ := lt_of_not_ge (fun h => hy ((mem_integers_iff_norm_le_one v y).2 h))
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hlt
      exact absurd hlt (by norm_num)
    have hinv : y⁻¹ ∈ v.adicCompletionIntegers F :=
      (mem_integers_iff_norm_le_one v _).2 (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hlt.le)
    have hmax : max 1 ‖y‖ = ‖y‖ := max_eq_right hlt.le
    rw [hmax, inv_sq_rpow_eq _ (by linarith), norm_mul, norm_mul, norm_modulusAtom v hy0]
    have hpow : (0 : ℝ) ≤ ‖y‖ ^ (-(2 * s.re + 1)) := Real.rpow_nonneg (by linarith) _
    calc ‖LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y‖
          * ‖y‖ ^ (-(2 * s.re + 1)) * ‖B y⁻¹‖
        ≤ 1 * ‖y‖ ^ (-(2 * s.re + 1)) * max CA CB := by
          gcongr
          · exact norm_charExt_le_one _ (norm_localChar_inv μ ν hμ hν v) y
          · exact (hCB _ hinv).trans (le_max_right _ _)
      _ = max CA CB * ‖y‖ ^ (-(2 * s.re + 1)) := by ring

variable {F} in

private theorem norm_unrFactor_le (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (v : HeightOneSpectrum (𝓞 F))
    (s : ℂ) (y : v.adicCompletion F) :
    ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt
                (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y‖
      ≤ ((max 1 ‖y‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) := by
  by_cases hy : y ∈ v.adicCompletionIntegers F
  · have hy' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_notMem
      (fun h => (show y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) from h) hy'), add_zero, norm_one]
    have hmax : max 1 ‖y‖ = 1 := max_eq_left ((mem_integers_iff_norm_le_one v y).1 hy)
    rw [hmax, inv_one, one_pow, Real.one_rpow]
  · have hy' : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
    rw [Set.indicator_of_notMem hy',
      Set.indicator_of_mem (show y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ from hy'),
      zero_add]
    have hlt : 1 < ‖y‖ := lt_of_not_ge (fun h => hy ((mem_integers_iff_norm_le_one v y).2 h))
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hlt
      exact absurd hlt (by norm_num)
    have hmax : max 1 ‖y‖ = ‖y‖ := max_eq_right hlt.le
    rw [hmax, inv_sq_rpow_eq _ (by linarith), norm_mul, norm_modulusAtom v hy0]
    calc ‖LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y‖
          * ‖y‖ ^ (-(2 * s.re + 1))
        ≤ 1 * ‖y‖ ^ (-(2 * s.re + 1)) :=
          mul_le_mul_of_nonneg_right (norm_charExt_le_one _ (norm_localChar_inv μ ν hμ hν v) y)
            (Real.rpow_nonneg (by linarith) _)
      _ = ‖y‖ ^ (-(2 * s.re + 1)) := one_mul _

variable {F} in

private theorem finite_nonIntegral (z : FiniteAdeleRing (𝓞 F) F) :
    {v : HeightOneSpectrum (𝓞 F) | z v ∉ v.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.mp z.2

variable {F} in

private theorem finHeightFactor_eq_one {v : HeightOneSpectrum (𝓞 F)} {y : v.adicCompletion F}
    (hy : y ∈ v.adicCompletionIntegers F) (σ : ℝ) : ((max 1 ‖y‖)⁻¹ ^ 2) ^ (σ + 1 / 2) = 1 := by
  rw [max_eq_left ((mem_integers_iff_norm_le_one v y).1 hy), inv_one, one_pow, Real.one_rpow]

variable {F} in
private theorem finHeightFactor_nonneg {v : HeightOneSpectrum (𝓞 F)} (y : v.adicCompletion F) (σ : ℝ) :
    0 ≤ ((max 1 ‖y‖)⁻¹ ^ 2) ^ (σ + 1 / 2) :=
  Real.rpow_nonneg (by positivity) _

private theorem finprod_rpow_eq {ι : Type} (h : ι → ℝ) (T : Finset ι) (hsupp : ∀ i, h i ≠ 1 → i ∈ T)
    (h0 : ∀ i, 0 ≤ h i) (r : ℝ) : (∏ᶠ i, h i) ^ r = ∏ i ∈ T, h i ^ r := by
  rw [finprod_eq_prod_of_mulSupport_subset h (s := T) (fun i hi => hsupp i hi),
    Real.finsetProd_rpow T h (fun i _ => h0 i) r]

variable {F} in
open scoped Classical in
private theorem archProduct_rpow (f : InfinitePlace F → ℝ) (hf : ∀ w, 0 ≤ f w) (r : ℝ) :
    (∏ w : InfinitePlace F, f w ^ w.mult) ^ r
      = (∏ i : {w : InfinitePlace F // w.IsReal}, f i.1 ^ r)
        * ∏ w : {w : InfinitePlace F // w.IsComplex}, (f w.1 ^ 2) ^ r := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)
      (fun w => f w ^ w.mult),
    Real.mul_rpow (Finset.prod_nonneg fun i _ => pow_nonneg (hf _) _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (hf _) _),
    ← Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hf _) _),
    ← Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hf _) _)]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : (i.1).mult = 1 := InfinitePlace.mult_isReal i
    rw [h1, pow_one]
  · refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w : InfinitePlace F =>
      InfinitePlace.not_isReal_iff_isComplex) _ _ fun b => ?_
    have h2 : (b.1).mult = 2 :=
      InfinitePlace.mult_isComplex ⟨b.1, InfinitePlace.not_isReal_iff_isComplex.1 b.2⟩
    show (f b.1 ^ (b.1).mult) ^ r = (f b.1 ^ 2) ^ r
    rw [h2]

variable {F} in

private theorem unrFactor_eq_one (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (s : ℂ) {y : v.adicCompletion F} (hy : y ∈ v.adicCompletionIntegers F) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt
                (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y = (1 : ℂ) := by
  have hy' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
  rw [Set.indicator_of_mem hy', Set.indicator_of_notMem
      (fun h => (show y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) from h) hy'), add_zero]

private theorem norm_pureTensorTerm_le
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (hRr : ∀ i (r : ℝ), 0 < r → ‖Rr i r‖ = 1) (hRc : ∀ w (r : ℝ), 0 < r → ‖Rc w r‖ = 1)
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
      (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
      ∀ y ∈ v.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x)
    (j : Fin n) (s : ℂ) :
    ∃ C : ℝ, ∀ x : AdeleRing (𝓞 F) F,
      ‖pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x‖
        ≤ C * ((∏ w : InfinitePlace F, ((1 + ‖x.1 w‖ ^ 2)⁻¹) ^ w.mult)
            * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((max 1 ‖x.2 v‖)⁻¹) ^ 2) ^ (s.re + 1 / 2) := by
  classical
  have hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : v.adicCompletion F,
      ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) y
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt
                  (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                * B j v y⁻¹) y‖
        ≤ C * ((max 1 ‖y‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) :=
    fun v hv => norm_sFactor_le μ ν hμ hν v (A j v) (B j v) m (hA j v hv) (hB j v hv) s
  choose! Cv hCv0 hCv using hS
  refine ⟨∏ v ∈ S, Cv v, fun x => ?_⟩
  set Tx : Finset (HeightOneSpectrum (𝓞 F)) := (finite_nonIntegral x.2).toFinset with hTx
  have hmemTx : ∀ v : HeightOneSpectrum (𝓞 F), x.2 v ∉ v.adicCompletionIntegers F → v ∈ Tx := by
    intro v hv
    rw [hTx, Set.Finite.mem_toFinset]
    exact hv
  set U : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ Tx.filter (fun v => v ∉ S) with hU
  have hdisj : Disjoint S (Tx.filter (fun v => v ∉ S)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_filter.1 hv').2 hv
  have hRHS : ((∏ w : InfinitePlace F, ((1 + ‖x.1 w‖ ^ 2)⁻¹) ^ w.mult)
        * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((max 1 ‖x.2 v‖)⁻¹) ^ 2) ^ (s.re + 1 / 2)
      = ((∏ i : {w : InfinitePlace F // w.IsReal}, (1 + ‖x.1 i.1‖ ^ 2)⁻¹ ^ (s.re + 1 / 2))
          * ∏ w : {w : InfinitePlace F // w.IsComplex}, ((1 + ‖x.1 w.1‖ ^ 2)⁻¹ ^ 2) ^ (s.re + 1 / 2))
        * ((∏ v ∈ S, ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2))
          * ∏ v ∈ Tx.filter (fun v => v ∉ S), ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2)) := by
    have hsuppU : ∀ v : HeightOneSpectrum (𝓞 F), ((max 1 ‖x.2 v‖)⁻¹) ^ 2 ≠ 1 → v ∈ U := by
      intro v hv
      by_contra hvU
      refine hv ?_
      have hint : x.2 v ∈ v.adicCompletionIntegers F := by
        by_contra hni
        exact hvU (Finset.mem_union.2 (Or.inr (Finset.mem_filter.2
          ⟨hmemTx v hni, fun hvS => hvU (Finset.mem_union.2 (Or.inl hvS))⟩)))
      rw [max_eq_left ((mem_integers_iff_norm_le_one v _).1 hint), inv_one, one_pow]
    rw [Real.mul_rpow (Finset.prod_nonneg fun w _ => pow_nonneg (inv_nonneg.mpr (by positivity)) _)
        (finprod_nonneg fun v => sq_nonneg _),
      archProduct_rpow (fun w => (1 + ‖x.1 w‖ ^ 2)⁻¹) (fun w => inv_nonneg.mpr (by positivity)),
      finprod_rpow_eq (fun v => ((max 1 ‖x.2 v‖)⁻¹) ^ 2) U hsuppU (fun v => sq_nonneg _), hU,
      Finset.prod_union hdisj]
  rw [hRHS]
  unfold pureTensorTerm
  rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod, norm_prod]
  have hreal : (∏ i : {w : InfinitePlace F // w.IsReal},
      ‖Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) ^ (-(1 / 2 : ℝ)))
        * ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ) - Complex.I)
            / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) : ℝ) : ℂ))
              ^ (kdat j i)
        * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))‖)
      = ∏ i : {w : InfinitePlace F // w.IsReal}, (1 + ‖x.1 i.1‖ ^ 2)⁻¹ ^ (s.re + 1 / 2) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_realFactor (Rr i) (hRr i) _ (kdat j i) s, sq_embReal]
  have hcomplex : (∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2) ^ (-(1 / 2 : ℝ)))
        * Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm j w).1
        * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1)) ^ (abm j w).2.1
        * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
            ^ (-(2 * s + 1) - ((abm j w).2.2 : ℂ) / 2)‖)
      ≤ ∏ w : {w : InfinitePlace F // w.IsComplex}, ((1 + ‖x.1 w.1‖ ^ 2)⁻¹ ^ 2) ^ (s.re + 1 / 2) := by
    refine Finset.prod_le_prod (fun w _ => norm_nonneg _) fun w _ => ?_
    rw [← norm_embComplex w.1 (x.1 w.1)]
    exact norm_complexFactor_le (Rc w) (hRc w) _ _ _ _ (habm j w) s
  have hSbound : (∏ v ∈ S,
      ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) (x.2 v)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt
                  (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                * B j v y⁻¹) (x.2 v)‖)
      ≤ (∏ v ∈ S, Cv v) * ∏ v ∈ S, ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v hv => hCv v hv (x.2 v)
  have hunr : ‖∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v.1)
        + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt
                (NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x.2 v.1))‖
      ≤ ∏ v ∈ Tx.filter (fun v => v ∉ S), ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) := by
    have hsub : (Function.mulSupport fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v.1)
          + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt
                  (NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x.2 v.1))
        ⊆ ↑(Tx.subtype fun v => v ∉ S) := by
      intro v hv
      rw [Function.mem_mulSupport] at hv
      rw [Finset.mem_coe, Finset.mem_subtype]
      by_contra hni
      refine hv (unrFactor_eq_one μ ν v.1 s ?_)
      by_contra hni'
      exact hni (hmemTx v.1 hni')
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, norm_prod,
      ← Finset.prod_subtype_eq_prod_filter (fun v => ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2))]
    exact Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ =>
      norm_unrFactor_le μ ν hμ hν v.1 s (x.2 v.1)
  rw [hreal]
  have hr0 : 0 ≤ ∏ i : {w : InfinitePlace F // w.IsReal}, (1 + ‖x.1 i.1‖ ^ 2)⁻¹ ^ (s.re + 1 / 2) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (inv_nonneg.mpr (by positivity)) _
  have hc0 : 0 ≤ ∏ w : {w : InfinitePlace F // w.IsComplex}, ((1 + ‖x.1 w.1‖ ^ 2)⁻¹ ^ 2) ^ (s.re + 1 / 2) :=
    Finset.prod_nonneg fun w _ => Real.rpow_nonneg (by positivity) _
  have hCS0 : 0 ≤ (∏ v ∈ S, Cv v) * ∏ v ∈ S, ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) :=
    mul_nonneg (Finset.prod_nonneg fun v hv => hCv0 v hv)
      (Finset.prod_nonneg fun v _ => finHeightFactor_nonneg _ _)
  calc _ ≤ (∏ i : {w : InfinitePlace F // w.IsReal}, (1 + ‖x.1 i.1‖ ^ 2)⁻¹ ^ (s.re + 1 / 2))
        * (∏ w : {w : InfinitePlace F // w.IsComplex}, ((1 + ‖x.1 w.1‖ ^ 2)⁻¹ ^ 2) ^ (s.re + 1 / 2))
        * ((∏ v ∈ S, Cv v) * ∏ v ∈ S, ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2))
        * ∏ v ∈ Tx.filter (fun v => v ∉ S), ((max 1 ‖x.2 v‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hcomplex hr0) hSbound
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) (mul_nonneg hr0 hc0)) hunr (norm_nonneg _) ?_
        exact mul_nonneg (mul_nonneg hr0 hc0) hCS0
    _ = _ := by ring

private theorem continuousOn_of_pin (R : ℝ → ℂ) (c : ℂ)
    (hc : ∀ b : ℝ, 0 < b → ∀ e : ℝ, R (b ^ e) = (b : ℂ) ^ ((e : ℂ) * c)) :
    ContinuousOn R (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun b : ℝ => (b : ℂ) ^ c) (Set.Ioi 0) := by
    intro b hb
    refine ContinuousAt.continuousWithinAt ?_
    exact Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 hb)
  refine hcont.congr fun b hb => ?_
  have h := hc b hb 1
  rw [Real.rpow_one, Complex.ofReal_one, one_mul] at h
  exact h

private theorem integrable_pureTensorTerm
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    (hχc : Continuous (μ * ν⁻¹))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
      (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (hm : 1 ≤ m)
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
      ∀ y ∈ v.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x)
    (hunr : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (hcond : ∀ v ∈ S, ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (hRr : ∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
      0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
      Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
        = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ))
    (hRc : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
      Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
      Rc w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ))
    (j : Fin n) :
    letI := adeleBorel (𝓞 F) F
    ∀ s : ℂ, 1 / 2 < s.re →
      Integrable (pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s) (adelicAddHaar (𝓞 F) F) := by
  have _ := hα
  have _ := hαdef
  have _ := hμic
  have _ := hνic
  have _ := hm
  intro s hs
  letI := adeleBorel (𝓞 F) F
  have hχu : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ‖(((μ * ν⁻¹) z : ℂˣ) : ℂ)‖ = 1 := fun z => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, hμ z, hν z, inv_one, mul_one]
  have hRr1 : ∀ (i : {w : InfinitePlace F // w.IsReal}) (r : ℝ), 0 < r → ‖Rr i r‖ = 1 := by
    intro i r hr
    obtain ⟨c, hc0, hc⟩ :=
      exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isReal F (μ * ν⁻¹) hχc hχu i (Rr i) (hRr i)
    exact norm_pin_eq_one (Rr i) c hc0 hc r hr
  have hRc1 : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (r : ℝ), 0 < r → ‖Rc w r‖ = 1 := by
    intro w r hr
    obtain ⟨c, hc0, hc⟩ :=
      exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isComplex F (μ * ν⁻¹) hχc hχu w (Rc w) (hRc w)
    exact norm_pin_eq_one (Rc w) c hc0 hc r hr
  have hRrc : ∀ i : {w : InfinitePlace F // w.IsReal}, ContinuousOn (Rr i) (Set.Ioi 0) := by
    intro i
    obtain ⟨c, -, hc⟩ :=
      exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isReal F (μ * ν⁻¹) hχc hχu i (Rr i) (hRr i)
    exact continuousOn_of_pin (Rr i) c hc
  have hRcc : ∀ w : {w : InfinitePlace F // w.IsComplex}, ContinuousOn (Rc w) (Set.Ioi 0) := by
    intro w
    obtain ⟨c, -, hc⟩ :=
      exists_re_eq_zero_and_forall_rpow_eq_cpow_of_isComplex F (μ * ν⁻¹) hχc hχu w (Rc w) (hRc w)
    exact continuousOn_of_pin (Rc w) c hc
  obtain ⟨hαpos, hone, hind⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hint := AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hαpos 1 1 hone hone
    s hs _ (hind hαpos s) (continuous_heightSection F s) 1
  obtain ⟨C, hC⟩ := norm_pureTensorTerm_le F μ ν hμ hν S n kdat abm m A B Rr Rc hRr1 hRc1 habm hA hB j s
  refine (hint.norm.const_mul C).mono'
    (aestronglyMeasurable_pureTensorTerm F μ ν S n kdat abm m A B Rr Rc hRrc hRcc hA hB hunr hcond j s)
    (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [norm_heightSection_weyl_unipotent]
  exact hC x

end WeylFlatContinuation.Local

namespace WeylFlatContinuation

variable (F : Type) [Field F] [NumberField F]

private theorem adelicGL2_ext {g g' : AdelicGL2 (𝓞 F) F}
    (harch : ∀ w : InfinitePlace F,
      archComponent F w (glArch (𝓞 F) F g) = archComponent F w (glArch (𝓞 F) F g'))
    (hfin : glFin (𝓞 F) F g = glFin (𝓞 F) F g') : g = g' := by
  ext i j
  refine Prod.ext ?_ ?_
  · funext w
    have h := congrArg (fun m : GL (Fin 2) w.Completion =>
      (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (harch w)
    exact h
  · have h := congrArg (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) hfin
    exact h

private theorem conj_mem_archRowIsometrySubgroup (w : InfinitePlace F) (k₀ : AdelicGL2 (𝓞 F) F)
    (hk₀ : IsRowIsometry (archComponent F w (glArch (𝓞 F) F k₀)))
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ archRowIsometrySubgroup F w) :
    k₀⁻¹ * k * k₀ ∈ archRowIsometrySubgroup F w := by
  rw [archRowIsometrySubgroup, Subgroup.mem_map] at hk ⊢
  obtain ⟨m, hm, rfl⟩ := hk
  set c : GL (Fin 2) w.Completion := archComponent F w (glArch (𝓞 F) F k₀) with hc
  have hcmem : c ∈ rowIsometrySubgroup w.Completion := mem_rowIsometrySubgroup_iff.2 hk₀
  refine ⟨c⁻¹ * m * c, mul_mem (mul_mem (inv_mem hcmem) hm) hcmem, ?_⟩
  apply adelicGL2_ext F
  · intro v
    by_cases hvw : v = w
    · subst hvw
      simp [adelicArchGLInclAt, glArch_adelicArchGLIncl, archComponent_archGLIncl_self, map_mul, map_inv,
        hc]
    ·
      simp [adelicArchGLInclAt, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne F hvw, map_mul,
        map_inv]
  ·
    simp [adelicArchGLInclAt, glFin_adelicArchGLIncl, map_mul, map_inv]

private theorem isArchKFinite_comp_mul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (k₀ : AdelicGL2 (𝓞 F) F)
    (hk₀ : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k₀)))
    (hφ : IsArchKFinite F φ) : IsArchKFinite F (fun x => φ (x * k₀)) := by
  intro w
  have h := hφ w
  unfold IsArchKFiniteAt RightTranslatesSpanFinite at h ⊢
  obtain ⟨s, hs⟩ := h
  classical
  let T : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun x : AdelicGL2 (𝓞 F) F => x * k₀)
  refine ⟨s.image T, fun k hk => ?_⟩
  have hk' : k₀⁻¹ * k * k₀ ∈ archRowIsometrySubgroup F w :=
    conj_mem_archRowIsometrySubgroup F w k₀ (hk₀ w) hk
  have hmem := hs _ hk'
  have heq : (fun x : AdelicGL2 (𝓞 F) F => (fun y : AdelicGL2 (𝓞 F) F => φ (y * k₀)) (x * k))
      = T (fun x : AdelicGL2 (𝓞 F) F => φ (x * (k₀⁻¹ * k * k₀))) := by
    funext x
    simp only [T, LinearMap.funLeft_apply]
    congr 1
    group
  rw [heq, Finset.coe_image, Submodule.span_image]
  exact Submodule.mem_map_of_mem hmem

private theorem isKfSmooth_comp_mul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (k₀ : AdelicGL2 (𝓞 F) F)
    (hk₀ : glFin (𝓞 F) F k₀ ∈ finiteIntegralGL2 (𝓞 F) F)
    (hφ : IsKfSmooth F φ) : IsKfSmooth F (fun x => φ (x * k₀)) := by
  have _ := hk₀
  unfold IsKfSmooth at hφ ⊢
  set v : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ := RightTranslationFn.mk φ with hv
  change IsSmoothVector (finiteAdelicGL2Subgroup F) (k₀ • v)
  unfold IsSmoothVector at hφ ⊢
  have hconj : ∀ h : finiteAdelicGL2Subgroup F,
      k₀⁻¹ * (h : AdelicGL2 (𝓞 F) F) * k₀ ∈ finiteAdelicGL2Subgroup F := by
    intro h
    rw [mem_finiteAdelicGL2Subgroup_iff]
    have hh : glArch (𝓞 F) F (h : AdelicGL2 (𝓞 F) F) = 1 := (mem_finiteAdelicGL2Subgroup_iff F _).1 h.2
    rw [map_mul, map_mul, map_inv, hh, mul_one, inv_mul_cancel]
  let c : finiteAdelicGL2Subgroup F → finiteAdelicGL2Subgroup F :=
    fun h => ⟨k₀⁻¹ * (h : AdelicGL2 (𝓞 F) F) * k₀, hconj h⟩
  have hc : Continuous c :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) hconj
  have hset : ((MulAction.stabilizer (finiteAdelicGL2Subgroup F) (k₀ • v) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F))
      = c ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup F) v :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := by
    ext h
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff, c, Subgroup.smul_def]
    constructor
    · intro hh
      calc (k₀⁻¹ * (h : AdelicGL2 (𝓞 F) F) * k₀) • v
            = k₀⁻¹ • (h : AdelicGL2 (𝓞 F) F) • k₀ • v := by rw [mul_smul, mul_smul]
        _ = k₀⁻¹ • k₀ • v := by rw [hh]
        _ = v := inv_smul_smul k₀ v
    · intro hh
      calc (h : AdelicGL2 (𝓞 F) F) • k₀ • v
            = k₀ • k₀⁻¹ • (h : AdelicGL2 (𝓞 F) F) • k₀ • v := (smul_inv_smul k₀ _).symm
        _ = k₀ • (k₀⁻¹ * (h : AdelicGL2 (𝓞 F) F) * k₀) • v := by rw [mul_smul, mul_smul]
        _ = k₀ • v := by rw [hh]
  rw [hset]
  exact hφ.preimage hc

private noncomputable def diagGL (p q : (AdeleRing (𝓞 F) F)ˣ) : AdelicGL2 (𝓞 F) F where
  val := !![(p : AdeleRing (𝓞 F) F), 0; 0, (q : AdeleRing (𝓞 F) F)]
  inv := !![((p⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0;
    0, ((q⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagGL_mem (p q : (AdeleRing (𝓞 F) F)ˣ) : diagGL F p q ∈ adelicBorel (𝓞 F) F := by
  show ((diagGL F p q : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  simp [diagGL]

private theorem borelDiagFst_diagGL (p q : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagGL F p q, diagGL_mem F p q⟩ : ↥(adelicBorel (𝓞 F) F)) = p := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  simp [diagGL]

private theorem borelDiagSnd_diagGL (p q : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagGL F p q, diagGL_mem F p q⟩ : ↥(adelicBorel (𝓞 F) F)) = q := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  simp [diagGL]

private theorem adelicWeyl_inv_eq : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

private theorem adelicWeyl_val :
    ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, 0] := by
  ext i j
  rw [adelicWeyl, globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

private theorem weyl_unipotent_mul_borel (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F)
    (a d : (AdeleRing (𝓞 F) F)ˣ) (y : AdeleRing (𝓞 F) F)
    (ha : a = borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))
    (hd : d = borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))
    (hy : y = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)
    (x : AdeleRing (𝓞 F) F) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * b
      = diagGL F d a * ((adelicWeyl (𝓞 F) F)⁻¹
          * unipotentGL2 (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
              * (y + x * (d : AdeleRing (𝓞 F) F)))) := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb
  have ha' : (a : AdeleRing (𝓞 F) F) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 := by
    rw [ha, borelDiagFst_apply_val]
  have hd' : (d : AdeleRing (𝓞 F) F) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 := by
    rw [hd, borelDiagSnd_apply_val]
  apply Units.ext
  simp only [Units.val_mul, adelicWeyl_inv_eq, adelicWeyl_val, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagGL, hb', ← ha', ← hd', hy]

open scoped Pointwise in

private theorem integral_comp_affine (G : AdeleRing (𝓞 F) F → ℂ) (u : (AdeleRing (𝓞 F) F)ˣ)
    (e : AdeleRing (𝓞 F) F) :
    letI := adeleBorel (𝓞 F) F
    ∫ x, G (e + (u : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)
      = ((distribHaarChar (AdeleRing (𝓞 F) F) u⁻¹ : ℝ≥0) : ℂ)
          * ∫ x, G x ∂(adelicAddHaar (𝓞 F) F) := by
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := by
    unfold adelicAddHaar
    infer_instance
  have hmap : Measure.map (⇑(MeasurableEquiv.smul (u : (AdeleRing (𝓞 F) F)ˣ))) (adelicAddHaar (𝓞 F) F)
      = ((distribHaarChar (AdeleRing (𝓞 F) F) u⁻¹ : ℝ≥0) : ENNReal) • adelicAddHaar (𝓞 F) F := by
    refine Measure.ext (fun t ht => ?_)
    rw [Measure.map_apply (MeasurableEquiv.smul (u : (AdeleRing (𝓞 F) F)ˣ)).measurable ht,
      Measure.smul_apply, smul_eq_mul,
      show ⇑(MeasurableEquiv.smul (u : (AdeleRing (𝓞 F) F)ˣ)) ⁻¹' t = u⁻¹ • t from
        Set.preimage_smul u t,
      ← distribHaarChar_mul]
  have h1 : ∫ x, G (e + (u : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)
      = ∫ x, (fun t => G (e + t)) ((MeasurableEquiv.smul (u : (AdeleRing (𝓞 F) F)ˣ)) x)
          ∂(adelicAddHaar (𝓞 F) F) := by
    rfl
  rw [h1, ← integral_map_equiv (MeasurableEquiv.smul (u : (AdeleRing (𝓞 F) F)ˣ))
    (fun t => G (e + t)), hmap, integral_smul_measure, integral_add_left_eq_self]
  rw [ENNReal.coe_toReal, Complex.real_smul]

private theorem weylIntegral_borel_mul_eq
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (b₀ k₀ : AdelicGL2 (𝓞 F) F) (hb₀ : b₀ ∈ adelicBorel (𝓞 F) F) :
    letI := adeleBorel (𝓞 F) F
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ s : ℂ,
      weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) (b₀ * k₀)
        = E s * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
            (fun x => φ s (x * k₀)) 1 := by
  letI := adeleBorel (𝓞 F) F
  set aU := borelDiagFst (⟨b₀, hb₀⟩ : ↥(adelicBorel (𝓞 F) F)) with haU
  set dU := borelDiagSnd (⟨b₀, hb₀⟩ : ↥(adelicBorel (𝓞 F) F)) with hdU
  set y₀ : AdeleRing (𝓞 F) F := (b₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 with hy₀
  have hmat := weyl_unipotent_mul_borel F b₀ hb₀ aU dU y₀ haU hdU hy₀
  set u : (AdeleRing (𝓞 F) F)ˣ := aU⁻¹ * dU with hu
  set e : AdeleRing (𝓞 F) F := ((aU⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y₀ with he
  have harg : ∀ x : AdeleRing (𝓞 F) F, ((aU⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      * (y₀ + x * (dU : AdeleRing (𝓞 F) F)) = e + (u : AdeleRing (𝓞 F) F) * x := by
    intro x
    simp only [he, hu, Units.val_mul]
    ring
  set C : ℂ := ((distribHaarChar (AdeleRing (𝓞 F) F) u⁻¹ : ℝ≥0) : ℂ) with hC
  refine ⟨fun s => ((etaFst μ α hα s dU : ℂˣ) : ℂ) * ((etaSnd ν α hα s aU : ℂˣ) : ℂ) * C,
    ?_, fun s => ?_⟩
  ·
    have hE : (fun s => ((etaFst μ α hα s dU : ℂˣ) : ℂ) * ((etaSnd ν α hα s aU : ℂˣ) : ℂ) * C)
        = fun s => ((μ dU : ℂˣ) : ℂ) * ((((α dU : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2))
            * (((ν aU : ℂˣ) : ℂ) * ((((α aU : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)))) * C := rfl
    rw [hE]
    have h1 : Differentiable ℂ (fun s : ℂ => (((α dU : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)) :=
      (differentiable_id.add_const _).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (hα dU).ne'))
    have h2 : Differentiable ℂ (fun s : ℂ => (((α aU : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2))) :=
      (differentiable_id.add_const _).neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (hα aU).ne'))
    exact (((differentiable_const _).mul h1).mul ((differentiable_const _).mul h2)).mul
      (differentiable_const _)
  ·
    have hlaw : ∀ x : AdeleRing (𝓞 F) F,
        φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (b₀ * k₀))
          = ((etaFst μ α hα s dU : ℂˣ) : ℂ) * ((etaSnd ν α hα s aU : ℂˣ) : ℂ)
            * φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (e + (u : AdeleRing (𝓞 F) F) * x)
                * k₀) := by
      intro x
      rw [← mul_assoc, hmat x, mul_assoc, hφ s _ (diagGL_mem F dU aU), borelDiagFst_diagGL,
        borelDiagSnd_diagGL, harg x]
    have hsub := integral_comp_affine F
      (fun t => φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 t * k₀)) u e
    calc weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) (b₀ * k₀)
        = ∫ x, ((etaFst μ α hα s dU : ℂˣ) : ℂ) * ((etaSnd ν α hα s aU : ℂˣ) : ℂ)
            * φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (e + (u : AdeleRing (𝓞 F) F) * x)
                * k₀) ∂(adelicAddHaar (𝓞 F) F) := by
          simp only [weylIntertwiningIntegral, hlaw]
      _ = ((etaFst μ α hα s dU : ℂˣ) : ℂ) * ((etaSnd ν α hα s aU : ℂˣ) : ℂ)
            * ∫ x, φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (e + (u : AdeleRing (𝓞 F) F) * x)
                * k₀) ∂(adelicAddHaar (𝓞 F) F) := integral_const_mul _ _
      _ = ((etaFst μ α hα s dU : ℂˣ) : ℂ) * ((etaSnd ν α hα s aU : ℂˣ) : ℂ)
            * (C * ∫ x, φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k₀)
                ∂(adelicAddHaar (𝓞 F) F)) := by rw [hC]; exact congrArg _ hsub
      _ = ((etaFst μ α hα s dU : ℂˣ) : ℂ) * ((etaSnd ν α hα s aU : ℂˣ) : ℂ) * C
            * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
                (fun x => φ s (x * k₀)) 1 := by
          simp only [weylIntertwiningIntegral, mul_one]; ring

private theorem exists_unit_uniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : (v.adicCompletion F)ˣ, Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
    rfl
  have hne : ((π : F) : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact WithZero.zero_ne_coe hπv
  exact ⟨Units.mk0 _ hne, hπv⟩

open scoped Classical in

private theorem pureTensor_pieces
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    (hχc : Continuous (μ * ν⁻¹))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ)
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
      (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (hm : 1 ≤ m)
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
      ∀ y ∈ v.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x)
    (hunr : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (hcond : ∀ v ∈ S, ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
      NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1)
    (hRr : ∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
      0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
      Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
        = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ))
    (hRc : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
      Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
      Rc w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ))
    (j : Fin n) :
    letI := adeleBorel (𝓞 F) F
    (∀ s : ℂ, 1 / 2 < s.re →
      Integrable (Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s) (adelicAddHaar (𝓞 F) F)) ∧
    ∃ M : ℂ → ℂ, MeromorphicOn M Set.univ ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        M s = ∫ x, Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x ∂(adelicAddHaar (𝓞 F) F) := by
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  refine ⟨Local.integrable_pureTensorTerm F α hα hαdef μ ν hμ hν hμic hνic hχc S n kdat abm m A B Rr Rc
    habm hm hA hB hunr hcond hRr hRc j, ?_⟩
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => ⟨rfl⟩
  let μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F) := fun v => Measure.addHaar
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), (μv v).IsAddHaarMeasure := fun v =>
    show (Measure.addHaar : Measure (v.adicCompletion F)).IsAddHaarMeasure from inferInstance
  choose ϖ hϖ using fun v : HeightOneSpectrum (𝓞 F) => exists_unit_uniformizer F v
  obtain ⟨Ma, hMa, hMaeq⟩ :=
    WeylFlatContinuation.Local.archFactor_meromorphic F μ ν hμ hν hχc (kdat j) (abm j) (habm j) Rr Rc hRr hRc
  have hSv : ∀ v : HeightOneSpectrum (𝓞 F), ∃ Mv : ℂ → ℂ, MeromorphicOn Mv Set.univ ∧
      (v ∈ S → ∀ s : ℂ, 1 / 2 < s.re →
        Mv s = (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹
          * ∫ y, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) y
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt
          (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
          * B j v y⁻¹) y) ∂(μv v)) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨Mv, hMv, hMveq⟩ := WeylFlatContinuation.Local.localFactor_meromorphic F μ ν hμ hν v (μv v) (ϖ v) (hϖ v)
        (hcond v hv) m hm (A j v) (B j v) (hA j v hv) (hB j v hv)
      exact ⟨Mv, hMv, fun _ => hMveq⟩
    · exact ⟨fun _ => 0, MeromorphicOn.const 0, fun h => absurd h hv⟩
  choose Mv hMv hMveq using hSv
  obtain ⟨Q, hQ, hQeq⟩ := WeylFlatContinuation.Local.eulerTail_meromorphic F μ ν hμ hν hμic hνic hχc S ϖ hϖ
  refine ⟨fun s => ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)
      * (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
      * Ma s * (∏ v ∈ S, Mv v s) * Q s, ?_, fun s hs => ?_⟩
  · exact ((((MeromorphicOn.const _).fun_mul (MeromorphicOn.const _)).fun_mul hMa).fun_mul
      (MeromorphicOn.fun_prod (fun v _ => hMv v))).fun_mul hQ
  · obtain ⟨_, hMas⟩ := hMaeq s hs
    obtain ⟨hP0, hQs⟩ := hQeq s hs
    have hχ₁ : ∀ v ∉ S, ‖((NumberField.TateGlobal.localChar (μ * ν⁻¹) v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1 :=
      fun v _ => (WeylFlatContinuation.Local.norm_localChar_eq_one F
        (WeylFlatContinuation.Local.isUnitaryChar_mul_inv F hμ hν) v (ϖ v)).le
    have hglob := LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
      F (adelicAddHaar (𝓞 F) F) S μv
      (fun y : mixedEmbedding.mixedSpace F =>
(∏ i : {w : InfinitePlace F // w.IsReal},
        Rr i ((1 + y.1 i ^ 2) ^ (-(1 / 2 : ℝ)))
        * ((((y.1 i : ℝ) : ℂ) - Complex.I)
        / ((Real.sqrt (1 + y.1 i ^ 2)
        : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + y.1 i ^ 2 : ℝ) : ℂ))
        ^ (-(s + 1 / 2)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
        Rc w ((1 + ‖y.2 w‖ ^ 2) ^ (-(1 / 2 : ℝ)))
        * y.2 w ^ (abm j w).1
        * (starRingEnd ℂ) (y.2 w) ^ (abm j w).2.1
        * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ))
        ^ (-(2 * s + 1) - ((abm j w).2.2 : ℂ) / 2)))
      (fun (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) =>
((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) y
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt
          (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
          * B j v y⁻¹) y))
      ϖ (fun v _ => hϖ v) (NumberField.TateGlobal.localChar (μ * ν⁻¹)) hunr hχ₁ s hs
    have hT : ∀ x : AdeleRing (𝓞 F) F,
        (fun y : mixedEmbedding.mixedSpace F =>
(∏ i : {w : InfinitePlace F // w.IsReal},
        Rr i ((1 + y.1 i ^ 2) ^ (-(1 / 2 : ℝ)))
        * ((((y.1 i : ℝ) : ℂ) - Complex.I)
        / ((Real.sqrt (1 + y.1 i ^ 2)
        : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + y.1 i ^ 2 : ℝ) : ℂ))
        ^ (-(s + 1 / 2)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
        Rc w ((1 + ‖y.2 w‖ ^ 2) ^ (-(1 / 2 : ℝ)))
        * y.2 w ^ (abm j w).1
        * (starRingEnd ℂ) (y.2 w) ^ (abm j w).2.1
        * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ))
        ^ (-(2 * s + 1) - ((abm j w).2.2 : ℂ) / 2))) (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
          * ((∏ v ∈ S, (fun (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) =>
((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) y
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt
          (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
          * B j v y⁻¹) y)) v (x.2 v))
            * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
              (fun _ => (1 : ℂ)) (x.2 v.1)
              + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt
              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
              (x.2 v.1)))
        = Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x := by
      intro x
      simp only [Local.pureTensorTerm, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, mul_assoc]
    simp_rw [hT] at hglob
    have hPS : (∏ v ∈ S, (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹
        * ∫ y, (fun (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) =>
((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) y
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt
          (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
          * B j v y⁻¹) y)) v y ∂(μv v)) = ∏ v ∈ S, Mv v s := by
      refine Finset.prod_congr rfl (fun v hv => ?_)
      rw [hMveq v hv s hs]
    rw [hPS, ← hQs] at hglob
    have hc : ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
        ⟨(adelicAddHaar_adelicBox_pos F).ne', (adelicAddHaar_adelicBox_lt_top F).ne⟩)
    have h2 : ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹
        * ∫ x, Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x ∂(adelicAddHaar (𝓞 F) F)
        = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
          * Ma s * (∏ v ∈ S, Mv v s) * Q s := by
      refine mul_right_cancel₀ hP0 ?_
      rw [hglob, hMas]
      ring
    calc ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)
          * (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
          * Ma s * (∏ v ∈ S, Mv v s) * Q s
        = ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)
          * (((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹
            * ∫ x, Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x ∂(adelicAddHaar (𝓞 F) F)) := by
          rw [h2]; ring
      _ = ∫ x, Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x ∂(adelicAddHaar (𝓞 F) F) := by
          rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

private theorem continuous_toUnits_of_continuous_val (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : Continuous fun a => ((χ a : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have hne : ∀ a, ((χ a : ℂˣ) : ℂ) ≠ 0 := fun a => (χ a).ne_zero
  have heq : (fun a => (((χ a)⁻¹ : ℂˣ) : ℂ)) = fun a => (((χ a : ℂˣ) : ℂ))⁻¹ := by
    funext a; simp
  rw [heq]
  exact h.inv₀ hne

private theorem continuous_diagGL_left : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => diagGL F a 1 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
      (!![(a : AdeleRing (𝓞 F) F), 0; 0, ((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Units.continuous_val, continuous_const]
  · show Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
      (!![((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0;
          0, (((1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Units.continuous_coe_inv, continuous_const]

private theorem continuous_diagGL_right : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => diagGL F 1 a := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
      (!![((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, (a : AdeleRing (𝓞 F) F)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Units.continuous_val, continuous_const]
  · show Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
      (!![(((1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0;
          0, ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Units.continuous_coe_inv, continuous_const]

private theorem continuous_mul_inv_of_ne_zero
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαdef : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hφc : ∀ s, Continuous (φ s))
    (hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      φ s k = φ s' k)
    (hne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0) :
    Continuous (μ * ν⁻¹) := by
  have _ := hαdef
  obtain ⟨s₀, g₀, hg₀⟩ := hne
  obtain ⟨b, k, hb, hkf, hkarch, rfl⟩ := exists_mem_adelicBorel_mul_eq F g₀
  have hk₀ : φ s₀ k ≠ 0 := by
    rw [hφ s₀ b hb k] at hg₀
    exact right_ne_zero_of_mul hg₀
  have hk : φ (-1 / 2 : ℂ) k ≠ 0 := by
    rw [hφflat (-1 / 2 : ℂ) s₀ k hkf hkarch]
    exact hk₀
  have h0 : (-1 / 2 : ℂ) + 1 / 2 = 0 := by norm_num
  have h0' : -((-1 / 2 : ℂ) + 1 / 2) = 0 := by rw [h0, neg_zero]
  have hμ : ∀ a : (AdeleRing (𝓞 F) F)ˣ,
      ((μ a : ℂˣ) : ℂ) = φ (-1 / 2 : ℂ) (diagGL F a 1 * k) / φ (-1 / 2 : ℂ) k := by
    intro a
    rw [eq_div_iff hk, hφ (-1 / 2 : ℂ) _ (diagGL_mem F a 1) k, borelDiagFst_diagGL, borelDiagSnd_diagGL,
      map_one, Units.val_one, mul_one]
    congr 1
    rw [etaFst_apply, Units.val_mul, cpowChar_apply_val, h0, Complex.cpow_zero, mul_one]
  have hν : ∀ a : (AdeleRing (𝓞 F) F)ˣ,
      ((ν a : ℂˣ) : ℂ) = φ (-1 / 2 : ℂ) (diagGL F 1 a * k) / φ (-1 / 2 : ℂ) k := by
    intro a
    rw [eq_div_iff hk, hφ (-1 / 2 : ℂ) _ (diagGL_mem F 1 a) k, borelDiagFst_diagGL, borelDiagSnd_diagGL,
      map_one, Units.val_one, one_mul]
    congr 1
    rw [etaSnd_apply, Units.val_mul, cpowChar_apply_val, h0', Complex.cpow_zero, mul_one]
  have hμc : Continuous fun a => ((μ a : ℂˣ) : ℂ) := by
    have : (fun a => ((μ a : ℂˣ) : ℂ))
        = fun a => φ (-1 / 2 : ℂ) (diagGL F a 1 * k) / φ (-1 / 2 : ℂ) k := funext hμ
    rw [this]
    exact ((hφc _).comp ((continuous_diagGL_left F).mul continuous_const)).div_const _
  have hνc : Continuous fun a => ((ν a : ℂˣ) : ℂ) := by
    have : (fun a => ((ν a : ℂˣ) : ℂ))
        = fun a => φ (-1 / 2 : ℂ) (diagGL F 1 a * k) / φ (-1 / 2 : ℂ) k := funext hν
    rw [this]
    exact ((hφc _).comp ((continuous_diagGL_right F).mul continuous_const)).div_const _
  apply continuous_toUnits_of_continuous_val F
  have heq : (fun a => ((((μ * ν⁻¹) a : ℂˣ)) : ℂ))
      = fun a => ((μ a : ℂˣ) : ℂ) * (((ν a : ℂˣ) : ℂ))⁻¹ := by
    funext a; simp
  rw [heq]
  exact hμc.mul (hνc.inv₀ fun a => (ν a).ne_zero)

end WeylFlatContinuation

open WeylFlatContinuation in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    ∃ M' : ℂ → ℂ, MeromorphicOn M' Set.univ
      ∧ ∀ s : ℂ, 1 / 2 < s.re → M' s
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by
  intro α hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφflat g
  letI := adeleBorel (𝓞 F) F
  by_cases hz : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), φ s x = 0
  · refine ⟨fun _ => 0, fun z _ => analyticAt_const.meromorphicAt, fun s _ => ?_⟩
    simp [weylIntertwiningIntegral, hz]
  push Not at hz
  obtain ⟨b₀, k₀, hb₀, hk₀f, hk₀a, rfl⟩ := exists_mem_adelicBorel_mul_eq F g
  set ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s x => φ s (x * k₀) with hψdef
  obtain ⟨E, hE, hEeq⟩ := weylIntegral_borel_mul_eq F α hα μ ν φ hφ b₀ k₀ hb₀
  have hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s) :=
    fun s => (hφ s).rightTranslate k₀
  have hψK : ∀ s, IsArchKFinite F (ψ s) := fun s => isArchKFinite_comp_mul_right F (φ s) k₀ hk₀a (hφK s)
  have hψf : ∀ s, IsKfSmooth F (ψ s) := fun s => isKfSmooth_comp_mul_right F (φ s) k₀ hk₀f (hφf s)
  have hψc : ∀ s, Continuous (ψ s) := fun s =>
    (Continuous.uncurry_left s (show Continuous (Function.uncurry φ) from hφjc)).comp
      (continuous_mul_const k₀)
  have hψflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      ψ s k = ψ s' k := by
    intro s s' k hkf hka
    refine hφflat s s' (k * k₀) ?_ (fun w => by simpa only [map_mul] using (hka w).mul (hk₀a w))
    rw [map_mul]
    exact Subgroup.mul_mem _ hkf hk₀f
  have hψne : ∃ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), ψ s x ≠ 0 := by
    obtain ⟨s, x, hx⟩ := hz
    exact ⟨s, x * k₀⁻¹, by simpa only [hψdef, inv_mul_cancel_right] using hx⟩
  have hχc : Continuous (μ * ν⁻¹) :=
    continuous_mul_inv_of_ne_zero F α hα rfl μ ν ψ hψ hψc hψflat hψne
  obtain ⟨S, n, c, kdat, abm, m, A, B, Rr, Rc, habm, hm, hA, hB, hunr, hcond, hRr, hRc, hbig⟩ :=
    bigCell_eq_sum_pureTensor_of_flat_family F hα μ ν ψ hψ hψK hψf hψc hψflat hψne
  have hP := fun j : Fin n => pureTensor_pieces F α hα rfl μ ν hμ hν hμic hνic hχc S n kdat abm m A B
    Rr Rc habm hm hA hB hunr hcond hRr hRc j
  choose hint M hMmer hMeq using hP
  refine ⟨fun s => E s * ∑ j, c j * M j s, ?_, ?_⟩
  · intro z hz'
    exact ((hE.analyticAt z).meromorphicAt).fun_mul
      (MeromorphicAt.fun_sum (s := Finset.univ)
        (fun j _ => (MeromorphicAt.const (c j) z).fun_mul (hMmer j z hz')))
  · intro s hs
    rw [hEeq s]
    show E s * ∑ j, c j * M j s = _
    congr 1
    symm
    have hT : ∀ x : AdeleRing (𝓞 F) F, ψ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * 1)
        = ∑ j, c j * Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x := by
      intro x
      rw [mul_one, hbig s x]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Local.pureTensorTerm, mul_assoc]
    calc weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) 1
        = ∫ x, ∑ j, c j * Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x
            ∂(adelicAddHaar (𝓞 F) F) := by
          simp only [weylIntertwiningIntegral, hT]
      _ = ∑ j, ∫ x, c j * Local.pureTensorTerm F μ ν S n kdat abm A B Rr Rc j s x
            ∂(adelicAddHaar (𝓞 F) F) :=
          integral_finsetSum Finset.univ (fun j _ => (hint j s hs).const_mul (c j))
      _ = ∑ j, c j * M j s := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [integral_const_mul, hMeq j s hs]

#print axioms solution

end S_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_flat_family
end P2MW
export P2MW.S_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_flat_family (solution)
