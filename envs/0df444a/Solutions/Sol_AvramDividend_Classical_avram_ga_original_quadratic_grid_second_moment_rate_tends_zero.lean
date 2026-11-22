-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_quadratic_grid_second_moment_rate_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:59:54.177406+00:00
-- url     : https://prove2.me/submissions/205ce312-06b8-4dda-ba2a-1ff35f30c3b7

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℕ → Ω → ℝ) (J : ℝ)
    (hRate : ∀ m : ℕ,
      (∫ ω, (U m ω) ^ 2 ∂P) ≤ J / ((m : ℝ) + 1)) :
    Tendsto (fun m : ℕ => ∫ ω, (U m ω) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hNonneg (m : ℕ) : 0 ≤ ∫ ω, (U m ω) ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg (U m ω))
  have hOne :
      Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hLimit :
      Tendsto (fun m : ℕ => J / ((m : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) := by
    convert hOne.const_mul J using 1 <;> simp [div_eq_mul_inv]
  exact squeeze_zero hNonneg hRate hLimit
