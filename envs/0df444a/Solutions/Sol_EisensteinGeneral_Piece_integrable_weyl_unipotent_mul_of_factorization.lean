-- Prove2me | solution 1 for EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d923e059-9481-5bf1-bab9-b58cc48c067e

import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Module.ZLattice.Basic
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Mathlib.MeasureTheory.Integral.Pi
import Theorems.Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod
import Theorems.Thm_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq
import Theorems.Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth
import Theorems.Thm_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Piece_integrable_weyl_unipotent_mul_of_factorization
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

section GlueHeads

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EgenGlue

private theorem ch_norm_realWeightIntegrand (k : ℤ) (w : ℂ) (t x : ℝ) :
    ‖((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))‖ = (1 + x ^ 2) ^ (-w.re) := by
  have hs : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hs
  have h1 : ‖(((x : ℝ) : ℂ) - Complex.I)‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 1
    simp
    try ring
  have h2 : ‖(((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ))‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsq]
  have hweight : ‖((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k‖ = 1 := by
    rw [norm_zpow, norm_div, h1, h2, div_self hsq.ne', one_zpow]
  have hchar : ‖Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [norm_mul, norm_mul, hweight, hchar, Complex.norm_cpow_eq_rpow_re_of_pos hs, Complex.neg_re,
    one_mul, mul_one]

private theorem ch_continuous_realWeightIntegrand (k : ℤ) (w : ℂ) (t : ℝ) :
    Continuous (fun x : ℝ => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) := by
  have hbase : Continuous (fun x : ℝ => (((1 + x ^ 2 : ℝ) : ℂ))) := by fun_prop
  have hsqrt : Continuous (fun x : ℝ => (((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ))) := by fun_prop
  have hquot : Continuous (fun x : ℝ => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ))) := by
    refine Continuous.div₀ (by fun_prop) hsqrt ?_
    intro x
    have : (0 : ℝ) < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have hweight : Continuous (fun x : ℝ => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k) := by
    apply hquot.zpow₀
    intro x
    left
    have : (0 : ℝ) < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    apply div_ne_zero
    · intro h
      have h1 := congrArg Complex.im h
      simp at h1
    · exact_mod_cast this.ne'
  have hpow : Continuous (fun x : ℝ => (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)) := by
    apply hbase.cpow continuous_const
    intro x
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hchar : Continuous (fun x : ℝ => Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) := by
    fun_prop
  exact (hweight.mul hpow).mul hchar

private theorem integrable_realWeightIntegrand (k : ℤ) (w : ℂ) (hw : 1 / 2 < w.re) (t : ℝ) :
    Integrable (fun x : ℝ => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) := by
  have hmaj : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * w.re) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq (E := ℝ)
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  refine hmaj.mono' (ch_continuous_realWeightIntegrand k w t).aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro x
  rw [ch_norm_realWeightIntegrand, Real.norm_eq_abs, sq_abs]
  apply le_of_eq
  congr 1
  ring

private theorem ch_norm_pow_le (z : ℂ) (n : ℕ) : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : ‖z‖ ^ n = (‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast ‖z‖ n, ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

private theorem ch_majorant_integrable (n : ℕ) (σ : ℝ) (hσ : (n : ℝ) / 2 + 1 < σ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)) := by
  have hnr : (Module.finrank ℝ ℂ : ℝ) < 2 * σ - n := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hnr).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)).aestronglyMeasurable
  · have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)
        ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (ch_norm_pow_le z n) (by positivity)
      _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ - n) / 2) := by
          rw [← Real.rpow_add hpos]
          congr 1
          ring

private theorem integrable_complexWeightIntegrand (a b : ℕ) (w : ℂ) (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) := by
  refine (ch_majorant_integrable (a + b) w.re hw).mono' ?_
    (Filter.Eventually.of_forall fun z => le_of_eq ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine ((Continuous.mul (continuous_id.pow a) (Complex.continuous_conj.pow b)).mul ?_).mul ?_
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun z => Complex.ofReal_mem_slitPlane.mpr (by positivity))
    · exact Complex.continuous_exp.comp (by fun_prop)
  · have hexp : ‖Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖ = 1 := by
      rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
      Complex.norm_cpow_eq_rpow_re_of_pos (x := 1 + ‖z‖ ^ 2) (by positivity) (-w), Complex.neg_re,
      hexp, mul_one, pow_add]

open scoped Classical in

private theorem integrable_mixedSpace_prod (F : Type) [Field F] [NumberField F]
    (f : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ) (h : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
    (hf : ∀ w, Integrable (f w)) (hh : ∀ w, Integrable (h w)) :
    Integrable (fun x : mixedEmbedding.mixedSpace F => (∏ w, f w (x.1 w)) * ∏ w, h w (x.2 w))
      MeasureTheory.volume := by
  have h1 : Integrable (fun x : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ w, f w (x w))
      (Measure.pi fun _ => volume) := Integrable.fintype_prod hf
  have h2 : Integrable (fun x : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w, h w (x w))
      (Measure.pi fun _ => volume) := Integrable.fintype_prod hh
  have h12 := h1.mul_prod h2
  exact h12

end EgenGlue

end GlueHeads

section PieceLayer

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

open scoped NNReal
open EisensteinGeneral

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EgenPiece

section Helpers

open Filter Topology

variable {F : Type} [Field F] [NumberField F]

private theorem pc_two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem pc_norm_mul_cpow_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℂ) (hc : ‖c‖ = 1) (s : ℂ)
    (hs : 0 < s.re) :
    ‖c * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
  have h2 := pc_two_le_absNorm v
  have hpos : 0 < Ideal.absNorm v.asIdeal := by omega
  rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos hpos]
  have hre : (-(2 * s)).re = -(2 * s.re) := by simp [Complex.mul_re]
  rw [hre]
  have h2' : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast h2
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

private theorem pc_excess_bounds (M q t I : ℝ) (hM : 0 < M) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (hI : I = M * (1 - 1 * q ^ (-(t + 1))) * (1 - 1 * q ^ (-t))⁻¹) :
    0 ≤ M⁻¹ * I - 1 ∧ M⁻¹ * I - 1 ≤ 2 * q ^ (-t) := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hx0 : 0 ≤ q ^ (-t) := Real.rpow_nonneg hq0.le _
  have hx10 : 0 ≤ q ^ (-(t + 1)) := Real.rpow_nonneg hq0.le _
  have hx1x : q ^ (-(t + 1)) ≤ q ^ (-t) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hxle : q ^ (-t) ≤ 1 / 2 := by
    calc q ^ (-t) ≤ q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = q⁻¹ := Real.rpow_neg_one q
      _ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hq
      _ = 1 / 2 := by norm_num
  have hden : 0 < 1 - q ^ (-t) := by linarith
  have hM' : M ≠ 0 := hM.ne'
  have hden' : 1 - q ^ (-t) ≠ 0 := hden.ne'
  have hkey : M⁻¹ * I - 1 = (q ^ (-t) - q ^ (-(t + 1))) * (1 - q ^ (-t))⁻¹ := by
    rw [hI]
    field_simp
    ring
  rw [hkey]
  have h2le : (1 - q ^ (-t))⁻¹ ≤ 2 := by
    calc (1 - q ^ (-t))⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
      _ = 2 := by norm_num
  constructor
  · exact mul_nonneg (by linarith) (inv_nonneg.mpr hden.le)
  · calc (q ^ (-t) - q ^ (-(t + 1))) * (1 - q ^ (-t))⁻¹ ≤ q ^ (-t) * 2 :=
          mul_le_mul (by linarith) h2le (inv_nonneg.mpr hden.le) hx0
      _ = 2 * q ^ (-t) := mul_comm _ _

private theorem pc_setOf_valued_sub_le_mem_nhds {v : HeightOneSpectrum (𝓞 F)} (x z : v.adicCompletion F)
    (hz : Valued.v z ≠ 0) :
    {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v z} ∈ 𝓝 x := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have hopen : IsOpen {w : v.adicCompletion F | Valued.v.restrict w ≤ Valued.v.restrict z} :=
    Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  have hopen' : IsOpen {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} := by
    simp
  refine Filter.mem_of_superset (hopen'.mem_nhds hx) fun y hy => ?_
  rw [Set.mem_setOf_eq, Valuation.restrict_le_iff] at hy
  exact hy

private theorem pc_valued_uniformizer_pow {v : HeightOneSpectrum (𝓞 F)} (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (m : ℕ) :
    Valued.v ((ϖ : v.adicCompletion F) ^ m) = (Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) := by
  have h1 : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  show _ = WithZero.exp (-(m : ℤ))
  rw [map_pow, h1, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem pc_continuousOn_integers_of_depth {v : HeightOneSpectrum (𝓞 F)} (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (m : ℕ)
    (A : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x) :
    ContinuousOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  have hz : Valued.v ((ϖ : v.adicCompletion F) ^ m) = (Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) :=
    pc_valued_uniformizer_pow ϖ hϖ m
  have hz0 : Valued.v ((ϖ : v.adicCompletion F) ^ m) ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  have hx1 : Valued.v x ≤ 1 := hx
  have hle1 : ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega
  apply ContinuousAt.continuousWithinAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [pc_setOf_valued_sub_le_mem_nhds x _ hz0] with y hy
  rw [hz] at hy
  have hy1 : y ∈ v.adicCompletionIntegers F := by
    show Valued.v y ≤ 1
    simpa [sub_add_cancel] using Valuation.map_add_le _ (hy.trans hle1) hx1
  exact (hA x hx y hy1 hy).symm

private theorem pc_isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  isCompact_iff_compactSpace.mpr (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F v)

private theorem pc_isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

private theorem pc_integrableOn_integers_of_depth {v : HeightOneSpectrum (𝓞 F)}
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (m : ℕ)
    (A : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x) :
    IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ :=
  (pc_continuousOn_integers_of_depth ϖ hϖ m A hA).integrableOn_compact (pc_isCompact_integers v)

private theorem pc_integrable_realWeight (k : ℤ) (τ : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun x : ℝ => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2))) := by
  have hw : 1 / 2 < (s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2).re := by
    have : (s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2).re = s.re + 1 / 2 := by
      norm_num [Complex.mul_re]
    rw [this]; linarith
  refine (EgenGlue.integrable_realWeightIntegrand k _ hw 0).congr (ae_of_all _ fun x => ?_)
  simp

private theorem pc_integrable_complexWeight (a b m : ℕ) (habm : a + b ≤ m) (τ : ℝ) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b
      * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + (m : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2))) := by
  have hw : ((a + b : ℕ) : ℝ) / 2 + 1 < (2 * s + 1 + (m : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2).re := by
    have hre : (2 * s + 1 + (m : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2).re
        = 2 * s.re + 1 + (m : ℝ) / 2 := by
      norm_num [Complex.mul_re]
    have hab : ((a + b : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast habm
    rw [hre]; linarith
  refine (EgenGlue.integrable_complexWeightIntegrand a b _ hw 0).congr (ae_of_all _ fun z => ?_)
  simp

private theorem pc_integrable_comp_smul (f : AdeleRing (𝓞 F) F → ℂ) (hf : Integrable f (adelicAddHaar (𝓞 F) F))
    (a : (AdeleRing (𝓞 F) F)ˣ) : Integrable (fun y => f (a • y)) (adelicAddHaar (𝓞 F) F) := by
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := by
    unfold adelicAddHaar
    infer_instance
  have hmap : Measure.map (Homeomorph.smul a).toMeasurableEquiv (adelicAddHaar (𝓞 F) F)
      = ((distribHaarChar (AdeleRing (𝓞 F) F) a⁻¹ : ℝ≥0) : ENNReal) • adelicAddHaar (𝓞 F) F := by
    ext t ht
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul (adelicAddHaar (𝓞 F) F) a⁻¹ t]
    change adelicAddHaar (𝓞 F) F ((fun x => a • x) ⁻¹' t) = _
    rw [Set.preimage_smul]
  have h1 : Integrable f (Measure.map (Homeomorph.smul a).toMeasurableEquiv (adelicAddHaar (𝓞 F) F)) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.coe_ne_top
  exact (integrable_map_equiv (Homeomorph.smul a).toMeasurableEquiv f).mp h1

private theorem pc_locallyCompactSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    LocallyCompactSpace (v.adicCompletion F) :=
  @locallyCompact_of_proper _ _ (NumberField.AdelicHaar.properSpace_adicCompletion (𝓞 F) F v)

private theorem pc_local_off (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (hχ1 : ‖((χ ϖ : ℂˣ) : ℂ)‖ = 1)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : 1 < s.re) (f : v.adicCompletion F → ℂ)
    (hf : ∀ x, f x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) :
    Integrable f μ ∧
      0 ≤ (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹ * (∫ y, ‖f y‖ ∂μ) - 1 ∧
      (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹ * (∫ y, ‖f y‖ ∂μ) - 1
        ≤ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hsv := pc_norm_mul_cpow_lt_one v _ hχ1 s hs0
  have hψ1 : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (0 : ℤ) →
      (1 : AddChar (v.adicCompletion F) ℂ) x = 1 :=
    fun x _ => AddChar.one_apply x
  have hL := LocalUnr.integrable_twisted_and_integral_norm_eq F v μ ϖ hϖ χ hχ s hsv 1 0 hψ1 0
  refine ⟨hL.1.congr (ae_of_all _ fun x => ?_), ?_⟩
  · rw [hf x]
    simp
  have hOfin : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ :=
    (pc_isCompact_integers v).measure_lt_top.ne
  have hOpos : 0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    ENNReal.toReal_pos
      ((pc_isOpen_integers v).measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne' hOfin
  have hL2 := hL.2
  rw [hχ1] at hL2
  have hnorm : ∫ y, ‖f y‖ ∂μ
      = μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        * (1 - 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)))
        * (1 - 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)))⁻¹ := by
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) hL2
    simp only []
    rw [hf x]
    simp
  have h2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast pc_two_le_absNorm v
  exact pc_excess_bounds _ _ _ _ hOpos h2 (by linarith) hnorm

private theorem pc_local_on (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (hχ1 : ‖((χ ϖ : ℂˣ) : ℂ)‖ = 1)
    (c : ℕ) (hc : 1 ≤ c) (hχc : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m) (A : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : 0 < s.re) (f : v.adicCompletion F → ℂ)
    (hf : ∀ x, f x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) :
    Integrable f μ := by
  have hsv := pc_norm_mul_cpow_lt_one v _ hχ1 s hs
  have hψ1 : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (0 : ℤ) →
      (1 : AddChar (v.adicCompletion F) ℂ) x = 1 :=
    fun x _ => AddChar.one_apply x
  have hA' := pc_integrableOn_integers_of_depth μ ϖ hϖ m A hA
  have hI := LocalRam.integrable_twisted_smooth F v μ ϖ hϖ χ c hc hχc m hm A hA' B hB s hsv 1 0 hψ1 0
  refine hI.congr (ae_of_all _ fun x => ?_)
  rw [hf x]
  simp

open scoped Classical in

private theorem pc_integrable_arch
    (kdat : {w : InfinitePlace F // w.IsReal} → ℤ) (τr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ) (τc : {w : InfinitePlace F // w.IsComplex} → ℝ)
    (habm : ∀ w : {w : InfinitePlace F // w.IsComplex}, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2)
    (Wr : {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
    (hWr : ∀ (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
      Wr i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr i : ℝ) : ℂ) * Complex.I / 2)))
    (Wc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
    (hWc : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
      Wc w s z = z ^ (abm w).1 * (starRingEnd ℂ) z ^ (abm w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm w).2.2 : ℂ) / 2 + ((τc w : ℝ) : ℂ) * Complex.I / 2)))
    (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun p : mixedEmbedding.mixedSpace F =>
      (∏ i : {w : InfinitePlace F // w.IsReal}, Wr i s (p.1 i))
        * ∏ w : {w : InfinitePlace F // w.IsComplex}, Wc w s (p.2 w)) MeasureTheory.volume :=
  EgenGlue.integrable_mixedSpace_prod F (fun i => Wr i s) (fun w => Wc w s)
    (fun i => (pc_integrable_realWeight (kdat i) (τr i) s hs).congr (ae_of_all _ fun x => (hWr i s x).symm))
    (fun w => (pc_integrable_complexWeight _ _ _ (habm w) (τc w) s hs).congr
      (ae_of_all _ fun z => (hWc w s z).symm))

open scoped Classical in

private theorem pc_integrable_affine (G : mixedEmbedding.mixedSpace F → ℂ) (hG : Integrable G MeasureTheory.volume)
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (Φ : FiniteAdeleRing (𝓞 F) F → ℂ) (hΦ : Integrable Φ ν) (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) :
    Integrable (fun y : AdeleRing (𝓞 F) F =>
      G (InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1) * Φ (a • (y + u)).2) (adelicAddHaar (𝓞 F) F) := by
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hH := Glue.integrable_mul_of_integrable_of_integrable F (adelicAddHaar (𝓞 F) F) ν G Φ hG hΦ
  have h1 := pc_integrable_comp_smul _ hH a
  have h2 := h1.comp_add_left u
  refine h2.congr (ae_of_all _ fun y => ?_)
  simp only [add_comm u y]

end Helpers

end EgenPiece

end PieceLayer

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open EgenPiece EisensteinGeneral EisensteinGeneral.Piece in
open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (D : FactorizationDatum F ψv nψ χ ϖ Ψ g S) :
    ∀ s : ℂ, 1 < s.re →
      Integrable (fun y => Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F) := by
  obtain ⟨cS, mS, n, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C, hχϖ, hχS, _, hcS, hχc, hmS, hA, hB, hoff, hon, habm,
    hWr, hWc, _, hfac⟩ := D
  intro s hs
  have hs0 : 0 < s.re := lt_trans one_pos hs
  haveI lcK : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => pc_locallyCompactSpace_adicCompletion v
  letI mK : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => borel _
  haveI bK : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => ⟨rfl⟩
  letI mA : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI bA : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

  have hint : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)),
      Integrable (h j v s) (Measure.addHaar : Measure (v.adicCompletion F)) := by
    intro j v
    by_cases hv : v ∈ S
    · exact pc_local_on v Measure.addHaar (ϖ v) (hϖ v) (NumberField.TateGlobal.localChar χ v) (hχϖ v) (cS v)
        (hcS v hv) (hχc v hv) mS hmS (A j v) (hA j v hv) (B j v) (hB j v hv) s hs0 (h j v s) (hon j v hv s)
    · exact (pc_local_off v Measure.addHaar (ϖ v) (hϖ v) (NumberField.TateGlobal.localChar χ v) (hχϖ v)
        (hχS v hv) s hs (h j v s) (hoff j v hv s)).1

  have hsum : ∀ j : Fin n, Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ((Measure.addHaar : Measure (v.1.adicCompletion F)).real
          (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))⁻¹
        * (∫ y, ‖h j v.1 s y‖ ∂(Measure.addHaar : Measure (v.1.adicCompletion F))) - 1 := fun j =>
    Summable.of_nonneg_of_le
      (fun v => (pc_local_off v.1 Measure.addHaar (ϖ v.1) (hϖ v.1) (NumberField.TateGlobal.localChar χ v.1)
        (hχϖ v.1) (hχS v.1 v.2) s hs (h j v.1 s) (hoff j v.1 v.2 s)).2.1)
      (fun v => (pc_local_off v.1 Measure.addHaar (ϖ v.1) (hϖ v.1) (NumberField.TateGlobal.localChar χ v.1)
        (hχϖ v.1) (hχS v.1 v.2) s hs (h j v.1 s) (hoff j v.1 v.2 s)).2.2)
      (((NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F (σ := 2 * s.re)
        (by linarith)).mul_left 2).comp_injective Subtype.val_injective)

  have hfin : ∀ j : Fin n,
      Integrable (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s (x v))
        (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 F) F)) := fun j =>
    (Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod F Measure.addHaar S
      (fun v => Measure.addHaar) (fun v => h j v s)
      (fun v hv y hy => by
        show h j v s y = 1
        rw [hoff j v hv s y]
        simp [hy])
      (hint j) (hsum j)).1

  have hT : ∀ j : Fin n, Integrable (fun y : AdeleRing (𝓞 F) F =>
      ((∏ i : {w : InfinitePlace F // w.IsReal},
          Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
          Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v)) (adelicAddHaar (𝓞 F) F) := fun j =>
    pc_integrable_affine
      (fun p : mixedEmbedding.mixedSpace F =>
        (∏ i : {w : InfinitePlace F // w.IsReal}, Wr j i s (p.1 i))
          * ∏ w : {w : InfinitePlace F // w.IsComplex}, Wc j w s (p.2 w))
      (pc_integrable_arch (kdat j) (τr j) (abm j) (τc j) (habm j) (Wr j) (hWr j) (Wc j) (hWc j) s hs)
      Measure.addHaar (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s (x v))
      (hfin j) a u

  have hS : Integrable (fun y : AdeleRing (𝓞 F) F => ∑ j : Fin n, C j s
      * (∏ i : {w : InfinitePlace F // w.IsReal},
          Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
      * (∏ w : {w : InfinitePlace F // w.IsComplex},
          Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v)) (adelicAddHaar (𝓞 F) F) := by
    refine integrable_finsetSum _ fun j _ => ?_
    refine ((hT j).const_mul (C j s)).congr (ae_of_all _ fun y => ?_)
    simp only []
    ring
  exact hS.congr (ae_of_all _ fun y => (hfac s y).symm)

end S_EisensteinGeneral_Piece_integrable_weyl_unipotent_mul_of_factorization
end P2MW
export P2MW.S_EisensteinGeneral_Piece_integrable_weyl_unipotent_mul_of_factorization (solution)
