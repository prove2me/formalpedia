-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.proposition_1_exp_utility
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:09:46.893624+00:00
-- url     : https://prove2.me/submissions/3eed5644-2ccb-403e-b294-27c4fa048198

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

open CryptoMembership.PerfectInfo MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExpUAux

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

end ExpUAux

namespace ExpUAux

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

end ExpUAux

open ExpUAux in
theorem solution (P : Params) (hP : P.Standing) (A a aStar : ℝ) :
    expUtility P A (Set.Ici aStar) a =
      Real.exp ((1 - P.eta) * a + P.eta * A + P.eta ^ 2 / (2 * P.tauEps)) *
        Phi (P.eta / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - aStar)) := by
  obtain ⟨-, -, hte, -, -, -⟩ := hP
  have hvε : (P.tauEps⁻¹).toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero, not_le] using hte
  have hpt : ∀ ε : ℝ, (Set.Ici aStar).indicator (fun Aj => matchUtility P.eta a Aj) (A + ε) =
      Real.exp ((1 - P.eta) * a + P.eta * A) *
        (Set.Ici (aStar - A)).indicator (fun y => Real.exp (P.eta * y)) ε := by
    intro ε
    by_cases h : aStar ≤ A + ε
    · rw [Set.indicator_of_mem (by simpa using h),
        Set.indicator_of_mem (by simp only [Set.mem_Ici]; linarith), matchUtility,
        ← Real.exp_add]
      congr 1; ring
    · rw [Set.indicator_of_notMem (by simpa using h),
        Set.indicator_of_notMem (by simp only [Set.mem_Ici]; intro h'; apply h; linarith)]
      simp
  rw [expUtility]
  simp_rw [hpt]
  rw [integral_const_mul, epsLaw, tilt_integral _ hvε, gauss_Ici _ _ hvε,
    Real.coe_toNNReal _ (inv_pos.2 hte).le, ← mul_assoc, ← Real.exp_add]
  have hs : 0 < Real.sqrt P.tauEps := Real.sqrt_pos.2 hte
  have hsq : Real.sqrt P.tauEps ^ 2 = P.tauEps := Real.sq_sqrt hte.le
  congr 2
  · field_simp
  · rw [Real.sqrt_inv]
    field_simp
    rw [hsq]
    ring
