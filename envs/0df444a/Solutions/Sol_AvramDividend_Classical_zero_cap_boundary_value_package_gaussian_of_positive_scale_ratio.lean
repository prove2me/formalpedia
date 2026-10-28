-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_boundary_value_package_gaussian_of_positive_scale_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:44:31.988326+00:00
-- url     : https://prove2.me/submissions/5b6c6782-fb40-4e47-9097-56a3e7e1f757

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The Gaussian scale origin and right slope leave only the positive-barrier
stochastic valuation to close the actual zero-cap boundary package. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1)))) :
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  have hC2 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  have hC1 : DifferentiableOn ℝ W (Ioi 0) :=
    hC2.differentiableOn (by norm_num)
  have hdiff : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x := by
    intro x hx
    have hxDiff : DifferentiableAt ℝ W x :=
      hC1.differentiableAt (isOpen_Ioi.mem_nhds hx)
    exact hxDiff.hasDerivAt
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hlimit : Tendsto (deriv W)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (2 / X.σ ^ 2)) := by
    simpa only [] using
      (scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
        X q hq W hW hσ hzero hdiff)
  have hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0 :=
    hW.2.2.1.continuousWithinAt (by simp)
  have hd : (2 : ℝ) / X.σ ^ 2 ≠ 0 := by
    have hsquared : 0 < X.σ ^ 2 := sq_pos_of_pos hσ
    exact ne_of_gt (div_pos (by norm_num) hsquared)
  exact zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
    X hX q hq W hW hscale hcont (Or.inl ⟨2 / X.σ ^ 2, hd, hlimit⟩)
