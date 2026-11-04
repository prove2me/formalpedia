-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.eq13_market_clearing
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:08:50.139244+00:00
-- url     : https://prove2.me/submissions/bd038708-aabe-45de-8358-031eee0eee14

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

open CryptoMembership.PerfectInfo MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Eq13Aux

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

end Eq13Aux

open Eq13Aux in
theorem solution (P : Params) (hP : P.Standing) (A xi a price : ℝ)
    (hprice : 0 < price) :
    buyerMass P A (Set.Ici a) = minerMass P xi price ↔
      Real.log price = Real.sqrt (P.tauEps / P.tauE) * (A - a) - xi - Real.log (1 - P.rho) := by
  obtain ⟨-, -, hte, hTe, -, hr1⟩ := hP
  have hvε : (P.tauEps⁻¹).toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero, not_le] using hte
  have hve : (P.tauE⁻¹).toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero, not_le] using hTe
  have h1r : 0 < 1 - P.rho := by linarith
  have hy : 0 < (1 - P.rho) * price := mul_pos h1r hprice
  have hset : {e : ℝ | Real.exp (-(xi + e)) ≤ (1 - P.rho) * price} =
      Set.Ici (-xi - Real.log ((1 - P.rho) * price)) := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    rw [← Real.le_log_iff_exp_le hy]
    constructor <;> intro h <;> linarith
  rw [buyerMass, minerMass, endowLaw, minerLaw, hset, gauss_Ici _ _ hvε, gauss_Ici _ _ hve,
    Phi_strictMono.injective.eq_iff]
  rw [Real.coe_toNNReal _ (inv_pos.2 hte).le, Real.coe_toNNReal _ (inv_pos.2 hTe).le,
    Real.sqrt_inv, Real.sqrt_inv, Real.log_mul h1r.ne' hprice.ne',
    Real.sqrt_div' _ hTe.le]
  have hs1 : 0 < Real.sqrt P.tauEps := Real.sqrt_pos.2 hte
  have hs2 : 0 < Real.sqrt P.tauE := Real.sqrt_pos.2 hTe
  rw [div_inv_eq_mul, div_inv_eq_mul]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring
