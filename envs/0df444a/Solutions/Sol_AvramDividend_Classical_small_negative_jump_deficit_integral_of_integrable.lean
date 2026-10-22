-- Prove2me | solution 1 for AvramDividend.Classical.small_negative_jump_deficit_integral_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:58:31.751998+00:00
-- url     : https://prove2.me/submissions/a30749f0-6c1c-4837-b82b-724590d69b0d

import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set

theorem solution
    (ν : Measure ℝ)
    (hint : IntegrableOn (fun y : ℝ => -y) (Ioo (-1 : ℝ) 0) ν) :
    Tendsto
      (fun θ : ℝ => ∫ y in Ioo (-1 : ℝ) 0,
        (1 - Real.exp (θ * y)) / θ ∂ν)
      atTop (nhds (0 : ℝ)) := by
  have hmem : ∀ᵐ y ∂(ν.restrict (Ioo (-1 : ℝ) 0)), y ∈ Ioo (-1 : ℝ) 0 :=
    ae_restrict_mem measurableSet_Ioo
  have key := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
    (μ := ν.restrict (Ioo (-1 : ℝ) 0))
    (F := fun (θ : ℝ) (y : ℝ) => (1 - Real.exp (θ * y)) / θ) (f := fun _ => (0 : ℝ))
    (fun y : ℝ => -y) ?_ ?_ hint ?_
  · simpa using key
  · refine Eventually.of_forall (fun θ => ?_)
    exact (by fun_prop : Continuous fun y : ℝ => (1 - Real.exp (θ * y)) / θ).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
    filter_upwards [hmem] with y hy
    have hy0 : y < 0 := hy.2
    have h1 : θ * y ≤ 0 := by nlinarith
    have h2 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr h1
    have h3 : 1 - Real.exp (θ * y) ≤ -(θ * y) := by linarith [Real.add_one_le_exp (θ * y)]
    have h4 : 0 ≤ (1 - Real.exp (θ * y)) / θ := div_nonneg (by linarith) hθ.le
    rw [Real.norm_eq_abs, abs_of_nonneg h4, div_le_iff₀ hθ]
    nlinarith
  · filter_upwards [hmem] with y hy
    have hy0 : y < 0 := hy.2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_inv_atTop_zero : Tendsto (fun θ : ℝ => θ⁻¹) atTop (nhds 0))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
      have h1 : θ * y ≤ 0 := by nlinarith
      have h2 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr h1
      exact div_nonneg (by linarith) hθ.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
      rw [← one_div]
      apply div_le_div_of_nonneg_right _ hθ.le
      linarith [Real.exp_pos (θ * y)]
