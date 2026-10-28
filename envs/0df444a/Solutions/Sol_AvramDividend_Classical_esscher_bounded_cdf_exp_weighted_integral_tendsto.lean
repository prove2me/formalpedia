-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_cdf_exp_weighted_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:06:08.410993+00:00
-- url     : https://prove2.me/submissions/1ce2f0d7-6c7b-4ba7-ab94-f06c6432b18f

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped ENNReal

/-- Exponentially weighted capital integrals preserve bounded pointwise CDF limits. -/
theorem solution
    (β : ℝ) (hβ : 0 < β)
    (F : ℕ → ℝ → ℝ) (L : ℝ → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFbound : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hlimit : ∀ x, Tendsto (fun n => F n x) atTop (nhds (L x))) :
    Tendsto (fun n => ∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * F n x ∂volume)
      atTop (nhds (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * L x ∂volume)) := by
  let Q : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hInt : Integrable (fun x : ℝ => Real.exp (-β * x)) Q := by
    change IntegrableOn (fun x : ℝ => Real.exp (-β * x)) (Ioi (0 : ℝ))
    exact integrableOn_exp_mul_Ioi (by linarith : -β < 0) 0
  have hmul : Measurable (fun x : ℝ => -β * x) :=
    measurable_const.mul measurable_id
  have hExp : Measurable (fun x : ℝ => Real.exp (-β * x)) :=
    Real.measurable_exp.comp hmul
  have hmeas (n : ℕ) :
      AEStronglyMeasurable
        (fun x : ℝ => Real.exp (-β * x) * F n x) Q :=
    (hExp.mul (hFmeas n)).aestronglyMeasurable
  have hbound (n : ℕ) :
      ∀ᵐ x ∂Q, ‖Real.exp (-β * x) * F n x‖ ≤
        Real.exp (-β * x) := by
    filter_upwards with x
    have he : 0 ≤ Real.exp (-β * x) := le_of_lt (Real.exp_pos _)
    have hf := hFbound n x
    calc
      ‖Real.exp (-β * x) * F n x‖ =
          Real.exp (-β * x) * F n x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg he hf.1)]
      _ ≤ Real.exp (-β * x) * 1 :=
        mul_le_mul_of_nonneg_left hf.2 he
      _ = Real.exp (-β * x) := mul_one _
  have hpt :
      ∀ᵐ x ∂Q,
        Tendsto (fun n : ℕ => Real.exp (-β * x) * F n x)
          atTop (nhds (Real.exp (-β * x) * L x)) :=
    Filter.Eventually.of_forall (fun x =>
      tendsto_const_nhds.mul (hlimit x))
  exact tendsto_integral_of_dominated_convergence
    (fun x : ℝ => Real.exp (-β * x)) hmeas hInt hbound hpt
