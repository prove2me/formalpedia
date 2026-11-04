-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.proposition_1_ex_ante_utility
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:15:34.337111+00:00
-- url     : https://prove2.me/submissions/8d6b1018-3b49-4c37-8915-4e1708501887

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model
import Theorems.Thm_CryptoMembership_PerfectInfo_proposition_1_exp_utility

open CryptoMembership.PerfectInfo MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExAnteAux

theorem std_map (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (gaussianReal μ v).map (fun x => (x - μ) / Real.sqrt (v : ℝ)) = gaussianReal 0 1 := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.1 h.symm))
  have : (fun x => (x - μ) / Real.sqrt (v : ℝ)) = (· / Real.sqrt (v : ℝ)) ∘ (· - μ) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
    gaussianReal_map_div_const]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt hv'.le, div_self hv'.ne']

theorem std_neg : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
  rw [gaussianReal_map_neg, neg_zero]

/-- `N(μ, v)([a, ∞)) = Φ((μ - a)/√v)`. -/
theorem gauss_Ici (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (a : ℝ) :
    (gaussianReal μ v).real (Set.Ici a) = Phi ((μ - a) / Real.sqrt (v : ℝ)) := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.1 h.symm))
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hv'
  rw [Phi, cdf_eq_real, ← std_neg, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Iic, ← std_map μ v hv,
    Measure.map_apply (by fun_prop) (measurableSet_Iic.preimage (by fun_prop))]
  congr 2
  ext x
  simp only [Set.mem_Ici, Set.mem_preimage, Set.mem_Iic]
  rw [neg_le, ← neg_div, neg_sub, div_le_div_iff_of_pos_right hs]
  constructor <;> intro h <;> linarith

theorem Phi_strictMono : StrictMono Phi := by
  intro x y hxy
  rw [Phi, Phi, cdf_eq_real, cdf_eq_real, ← Set.Iic_union_Ioc_eq_Iic hxy.le,
    measureReal_union (Set.disjoint_left.2 fun t ht ht' => by
      simp only [Set.mem_Iic, Set.mem_Ioc] at ht ht'; linarith) measurableSet_Ioc]
  have : 0 < (gaussianReal 0 1).real (Set.Ioc x y) := by
    rw [measureReal_def]
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h0
    rw [Real.volume_Ioc] at this
    simp at this
    linarith
  linarith

end ExAnteAux
namespace ExAnteAux

theorem pdf_tilt (v : ℝ≥0) (hv : v ≠ 0) (t x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp (t * x) =
      Real.exp (t ^ 2 * v / 2) * gaussianPDFReal (t * v) v x := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.1 h.symm))
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  simp only
  rw [mul_comm (Real.exp (t ^ 2 * v / 2)), mul_assoc, mul_assoc, ← Real.exp_add]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- Exponential tilting of a centred Gaussian over a half-line. -/
theorem tilt_integral (v : ℝ≥0) (hv : v ≠ 0) (t c : ℝ) :
    ∫ x, (Set.Ici c).indicator (fun y => Real.exp (t * y)) x ∂(gaussianReal 0 v) =
      Real.exp (t ^ 2 * v / 2) * (gaussianReal (t * v) v).real (Set.Ici c) := by
  rw [integral_gaussianReal_eq_integral_smul hv, ← integral_indicator_one measurableSet_Ici,
    integral_gaussianReal_eq_integral_smul hv, ← integral_const_mul]
  congr 1
  funext x
  simp only [smul_eq_mul]
  by_cases hx : x ∈ Set.Ici c
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, pdf_tilt v hv, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

end ExAnteAux

open ExAnteAux in
theorem solution (P : Params) (hP : P.Standing) (A a price : ℝ)
    (hindiff : expUtility P A (Set.Ici a) a = price) :
    exAnteUtility P A (Set.Ici a) price =
      Real.exp (A + ((1 - P.eta) ^ 2 + P.eta ^ 2) / (2 * P.tauEps)) *
          Phi ((1 - P.eta) / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a)) *
          Phi (P.eta / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a)) -
        price * Phi (Real.sqrt P.tauEps * (A - a)) := by
  have hte := hP.2.2.1
  have h1η : 0 < 1 - P.eta := by linarith [hP.2.1]
  set v := (P.tauEps⁻¹).toNNReal with hvdef
  have hv : v ≠ 0 := by simpa [v, Real.toNNReal_eq_zero, not_le] using hte
  have hvR : (v : ℝ) = P.tauEps⁻¹ := Real.coe_toNNReal _ (inv_pos.2 hte).le
  set q := P.eta ^ 2 / (2 * P.tauEps)
  set Φu := Phi (P.eta / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a))
  have hΦu : 0 ≤ Φu := cdf_nonneg _ _
  have hEU : ∀ x, expUtility P A (Set.Ici a) x =
      Real.exp (P.eta * A + q) * Φu * Real.exp ((1 - P.eta) * x) := by
    intro x
    rw [proposition_1_exp_utility P hP A x a]
    rw [mul_comm _ Φu, mul_comm (Real.exp (P.eta * A + q)) Φu, mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hmax : ∀ x, max (expUtility P A (Set.Ici a) x - price) 0 =
      (Set.Ici a).indicator (fun x => expUtility P A (Set.Ici a) x - price) x := by
    intro x
    rw [← hindiff]
    simp only [hEU]
    have hC : 0 ≤ Real.exp (P.eta * A + q) * Φu := mul_nonneg (Real.exp_pos _).le hΦu
    by_cases hx : a ≤ x
    · rw [Set.indicator_of_mem (by simpa using hx)]
      apply max_eq_left
      rw [sub_nonneg]
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx h1η.le)
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      apply max_eq_right
      rw [sub_nonpos]
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_of_not_ge hx) h1η.le)
  have hlaw : endowLaw P A = gaussianReal A v := rfl
  have : IsProbabilityMeasure (endowLaw P A) := by rw [hlaw]; infer_instance
  have hint : Integrable (fun x => Real.exp ((1 - P.eta) * x)) (endowLaw P A) := by
    rw [hlaw]; exact integrable_exp_mul_gaussianReal _
  -- the integral of e^{(1-η)x} over [a, ∞)
  have htail : ∫ x, (Set.Ici a).indicator (fun x => Real.exp ((1 - P.eta) * x)) x
      ∂(endowLaw P A) = Real.exp ((1 - P.eta) * A) *
        (Real.exp ((1 - P.eta) ^ 2 * v / 2) *
          (gaussianReal ((1 - P.eta) * v) v).real (Set.Ici (a - A))) := by
    rw [hlaw, ← zero_add A, ← gaussianReal_map_add_const A,
      integral_map (measurable_add_const A).aemeasurable
        ((by fun_prop : Continuous fun x => Real.exp ((1 - P.eta) * x)).measurable.indicator
          measurableSet_Ici).aestronglyMeasurable,
      ← tilt_integral v hv, ← integral_const_mul, zero_add]
    congr 1
    funext y
    by_cases hy : a ≤ y + A
    · rw [Set.indicator_of_mem (by simpa using hy),
        Set.indicator_of_mem (by simp only [Set.mem_Ici]; linarith), ← Real.exp_add]
      congr 1; ring
    · rw [Set.indicator_of_notMem (by simpa using hy),
        Set.indicator_of_notMem (by simp only [Set.mem_Ici]; intro h; apply hy; linarith),
        mul_zero]
  unfold exAnteUtility
  simp_rw [hmax]
  rw [integral_indicator measurableSet_Ici]
  simp_rw [hEU]
  rw [integral_sub (hint.const_mul _).integrableOn (integrable_const _).integrableOn,
    setIntegral_const, integral_const_mul, ← integral_indicator measurableSet_Ici, htail]
  rw [gauss_Ici _ _ hv, hlaw, gauss_Ici _ _ hv, smul_eq_mul, hvR]
  have hs : 0 < Real.sqrt P.tauEps := Real.sqrt_pos.2 hte
  have hsq : Real.sqrt P.tauEps ^ 2 = P.tauEps := Real.sq_sqrt hte.le
  have harg1 : ((1 - P.eta) * P.tauEps⁻¹ - (a - A)) / Real.sqrt P.tauEps⁻¹ =
      (1 - P.eta) / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a) := by
    rw [Real.sqrt_inv]; field_simp; rw [hsq]; ring
  have harg2 : (A - a) / Real.sqrt P.tauEps⁻¹ = Real.sqrt P.tauEps * (A - a) := by
    rw [Real.sqrt_inv]; field_simp
  rw [harg1, harg2]
  have hexp : Real.exp (P.eta * A + q) * Real.exp ((1 - P.eta) * A) *
      Real.exp ((1 - P.eta) ^ 2 * P.tauEps⁻¹ / 2) =
      Real.exp (A + ((1 - P.eta) ^ 2 + P.eta ^ 2) / (2 * P.tauEps)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [q]
    field_simp
    ring
  rw [← hexp]
  ring
