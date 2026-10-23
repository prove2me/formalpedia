-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_real_laplace_integral_eq_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:12:37.383673+00:00
-- url     : https://prove2.me/submissions/5e028365-08a6-4c02-9ea8-43a3ac953097

import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_inner_laplace_weight_factor
import Theorems.Thm_AvramDividend_Classical_real_weighted_laplace_toReal_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hfin : (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume) < ⊤) :
    (∫ t : ℝ, Real.exp (-θ * t) *
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ).toReal ∂volume) =
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume).toReal := by
  let F : ℝ → ENNReal := fun t =>
    ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ
  have hpos : MeasurableSet {p : ℝ × ℝ | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hlt : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} :=
    hpos.inter hlt
  have hprod : Measurable
      (fun p : ℝ × ℝ =>
        ENNReal.ofReal (p.2 - p.1) *
          ENNReal.ofReal (Real.exp (-φ * p.2))) := by
    fun_prop
  have hpair : Measurable
      (fun p : ℝ × ℝ =>
        if 0 < p.1 ∧ p.1 < p.2 then
          ENNReal.ofReal (p.2 - p.1) *
            ENNReal.ofReal (Real.exp (-φ * p.2))
        else 0) :=
    Measurable.ite hset hprod measurable_const
  have hF : Measurable F := Measurable.lintegral_prod_right hpair
  have hfactor :
      (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-θ * t)) * F t ∂volume) =
        (∫⁻ t : ℝ, ∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ ∂volume) := by
    apply lintegral_congr
    intro t
    exact (gaussian_double_tail_inner_laplace_weight_factor μ φ θ t).symm
  have hfint :
      (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-θ * t)) * F t ∂volume) < ⊤ := by
    rw [hfactor]
    exact hfin
  calc
    (∫ t : ℝ, Real.exp (-θ * t) * (F t).toReal ∂volume) =
      (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-θ * t)) * F t ∂volume).toReal := by
        simpa only [neg_mul] using
          (real_weighted_laplace_toReal_bridge volume θ F hF
            (by simpa only [neg_mul] using hfint))
    _ = (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume).toReal := by rw [hfactor]
