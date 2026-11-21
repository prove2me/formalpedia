-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_nonnegative_sqrt_grid_rate_implies_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:31:08.808246+00:00
-- url     : https://prove2.me/submissions/1a20dcfb-accb-4f3c-80cd-b826df21fd96

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- Quantitative root-physical-mesh bounds force nonnegative
original Gaussian expected rightatom errors to vanish. -/
theorem solution
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hRate : ∀ m : ℕ, a m ≤
      K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ))) :
    Tendsto a atTop (𝓝 (0 : ℝ)) := by
  have hInv : Tendsto (fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hΔ : Tendsto (fun m : ℕ =>
      (n : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using hInv.const_mul (n : ℝ)
  have hS : Tendsto (fun m : ℕ =>
      Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hΔ
  have hUpper : Tendsto (fun m : ℕ =>
      K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hS.const_mul K
  exact squeeze_zero ha hRate hUpper
