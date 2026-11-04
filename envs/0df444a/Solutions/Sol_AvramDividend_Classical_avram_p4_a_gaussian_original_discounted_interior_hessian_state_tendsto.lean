-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_interior_hessian_state_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:33:50.288619+00:00
-- url     : https://prove2.me/submissions/f7d0f978-94fc-4206-b6a7-9e91f6607ae1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- Along state approximations converging to a strict interior reserve,
the source-discounted Gaussian Hessian converges. This uses the source C2
hypothesis only at the limiting interior point. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (y : ℝ) (hy : 0 < y ∧ ENNReal.ofReal y < C)
    (s : ℝ≥0) (yn : ℕ → ℝ)
    (hyn : Tendsto yn atTop (nhds y)) :
    Tendsto (fun n => Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (yn n)))
      atTop (nhds (Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y))) := by
  have hOpen : IsOpen {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} :=
    avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C
  have hC2 : ContDiffAt ℝ 2 w y :=
    hwC2.contDiffAt (hOpen.mem_nhds hy)
  have hC1 : ContDiffAt ℝ 1 (deriv w) y :=
    hC2.derivWithin (by norm_num)
  have hC0 : ContDiffAt ℝ 0 (deriv (deriv w)) y :=
    hC1.derivWithin (by norm_num)
  have hId : iteratedDeriv 2 w = deriv (deriv w) := by
    calc
      iteratedDeriv 2 w = iteratedDeriv (1 + 1) w := by norm_num
      _ = deriv (iteratedDeriv 1 w) := by rw [iteratedDeriv_succ]
      _ = deriv (deriv w) := by rw [iteratedDeriv_one]
  have hCont : ContinuousAt (iteratedDeriv 2 w) y := by
    rw [hId]
    exact hC0.continuousAt
  have hProduct : ContinuousAt (fun z : ℝ =>
      Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w z)) y := by
    exact continuousAt_const.mul (continuousAt_const.mul hCont)
  exact hProduct.tendsto.comp hyn
