-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_full_normalized_exp_deficit_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:16:31.544812+00:00
-- url     : https://prove2.me/submissions/f138c0fd-9a75-443e-87d0-ef7968da2ddd

import Theorems.Thm_AvramDividend_Classical_small_negative_jump_deficit_integral_of_integrable
import Theorems.Thm_AvramDividend_Classical_negative_exponential_quotient_bounds
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open AvramDividend.Classical

/-- Normalised negative-jump exponential deficits vanish under truncated first-moment integrability. -/
theorem solution
    (ν : Measure ℝ)
    (hint : IntegrableOn (fun y : ℝ => min 1 |y|) (Iio (0 : ℝ)) ν) :
    Tendsto
      (fun θ : ℝ => ∫ y in Iio (0 : ℝ),
        (1 - Real.exp (θ * y)) / θ ∂ν)
      atTop (nhds (0 : ℝ)) := by
  have hmem :
      ∀ᵐ y ∂(ν.restrict (Iio (0 : ℝ))), y ∈ Iio (0 : ℝ) :=
    ae_restrict_mem measurableSet_Iio
  have key := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ))
    (μ := ν.restrict (Iio (0 : ℝ)))
    (F := fun (θ : ℝ) (y : ℝ) => (1 - Real.exp (θ * y)) / θ)
    (f := fun _ => (0 : ℝ))
    (fun y : ℝ => min 1 |y|) ?_ ?_ hint ?_
  · simpa using key
  · refine Eventually.of_forall (fun θ => ?_)
    exact (by fun_prop :
      Continuous fun y : ℝ => (1 - Real.exp (θ * y)) / θ).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with θ hθ
    filter_upwards [hmem] with y hy
    have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
    have hq := negative_exponential_quotient_bounds θ y hθ0 hy
    rw [Real.norm_eq_abs, abs_of_nonneg hq.1]
    apply le_min
    · apply (div_le_iff₀ hθ0).mpr
      nlinarith [Real.exp_pos (θ * y)]
    · exact hq.2
  · filter_upwards [hmem] with y hy
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (tendsto_inv_atTop_zero :
        Tendsto (fun θ : ℝ => θ⁻¹) atTop (nhds 0))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
      exact (negative_exponential_quotient_bounds θ y hθ hy).1
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
      rw [← one_div]
      apply div_le_div_of_nonneg_right _ hθ.le
      linarith [Real.exp_pos (θ * y)]
