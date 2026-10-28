-- Prove2me | solution 1 for AvramDividend.Classical.esscher_probability_weighted_cdf_real_eq_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T20:09:18.974238+00:00
-- url     : https://prove2.me/submissions/9b7cca48-d089-479e-86f9-497d20037d3d

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- On nonnegative laws, the real weighted CDF integral is exactly the
    ENNReal Laplace transform of the law, divided by its positive rate. -/
theorem solution
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ν (Iio (0 : ℝ)) = 0)
    (β : ℝ) (hβ : 0 < β) :
    ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
      Real.exp (-β * x) * cdf ν x ∂volume) = ENNReal.ofReal (1 / β) *
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) := by
  let Q : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hExp : Measurable (fun x : ℝ => Real.exp (-β * x)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hcdf : Measurable (cdf ν) := (monotone_cdf (μ := ν)).measurable
  have hIntExp : Integrable (fun x : ℝ => Real.exp (-β * x)) Q := by
    change IntegrableOn (fun x : ℝ => Real.exp (-β * x)) (Ioi (0 : ℝ))
    exact integrableOn_exp_mul_Ioi (by linarith : -β < 0) 0
  have hbound :
      ∀ᵐ x ∂Q, ‖Real.exp (-β * x) * cdf ν x‖ ≤
        Real.exp (-β * x) := by
    filter_upwards with x
    have hf0 := cdf_nonneg (μ := ν) x
    have hf1 := cdf_le_one (μ := ν) x
    have he : 0 ≤ Real.exp (-β * x) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg he hf0)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf1 he
  have hInt :
      Integrable (fun x : ℝ => Real.exp (-β * x) * cdf ν x) Q :=
    hIntExp.mono' (hExp.mul hcdf).aestronglyMeasurable hbound
  have hnonneg : ∀ᵐ x ∂Q,
      0 ≤ Real.exp (-β * x) * cdf ν x :=
    Filter.Eventually.of_forall (fun x =>
      mul_nonneg (Real.exp_pos _).le (cdf_nonneg (μ := ν) x))
  have hreal :
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
      Real.exp (-β * x) * cdf ν x ∂volume) =
      (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-β * x) * cdf ν x) ∂volume) :=
    ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  have hpoint (x : ℝ) :
      ENNReal.ofReal (Real.exp (-β * x) * cdf ν x) =
        ENNReal.ofReal (Real.exp (-β * x)) * ν (Iic x) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [ofReal_cdf ν x]
  calc
    ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
      Real.exp (-β * x) * cdf ν x ∂volume) =
      (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-β * x) * cdf ν x) ∂volume) := hreal
    _ = (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-β * x)) * ν (Iic x) ∂volume) := by
          refine lintegral_congr_ae ?_
          filter_upwards with x
          exact hpoint x
    _ = ENNReal.ofReal (1 / β) *
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) :=
      positiveLaplace_cumulative_measure ν β hβ hsupp
