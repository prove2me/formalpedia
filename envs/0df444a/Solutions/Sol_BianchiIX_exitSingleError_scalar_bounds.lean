-- Prove2me | solution 1 for BianchiIX.exitSingleError_scalar_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:51:39.300211+00:00
-- url     : https://prove2.me/submissions/2c0ad167-1d9a-402f-ba12-ee8a2d8e5564

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- The perturbation retains both small old walls; its radial coefficient has no zeroth-order term. -/
theorem solution {α R H T L K : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hR : 0 ≤ R ∧ R ≤ 5) (hH : α ^ 2 ≤ H) (hT : |T| ≤ α ^ 2 / 1000)
    (hN : |R ^ 2 - 4 + T| ≤ 22 * α) (hL : |L| ≤ 20 * α)
    (hK : |T| ≤ K) :
    |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ 23 * K / α ∧
      |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ 23 * α / 1000 ∧
      |T * (2 * R / H - (R ^ 2 - 4 + T) * L / H ^ 2)| ≤ 450 * K / α ^ 2 ∧
      |1 + (R ^ 2 - 4 + 2 * T) / H| ≤ 24 / α := by
  have hα0 := hα.1
  have hR0 := hR.1
  have hRhi := hR.2
  have hH0 : 0 < H := lt_of_lt_of_le (sq_pos_of_pos hα0) hH
  have hK0 : 0 ≤ K := (abs_nonneg T).trans hK
  have Hfactor : |1 + (R ^ 2 - 4 + T) / H| ≤ 23 / α := by
    calc
      _ ≤ 1 + |R ^ 2 - 4 + T| / H := by
        have Ha : |1 + (R ^ 2 - 4 + T) / H| ≤ |(1 : ℝ)| + |(R ^ 2 - 4 + T) / H| := abs_add_le _ _
        simpa only [abs_one, abs_div, abs_of_pos hH0] using Ha
      _ ≤ 1 + 22 * α / α ^ 2 := by gcongr
      _ ≤ 23 / α := by
        apply (le_div_iff₀ hα0).mpr
        field_simp
        nlinarith only [hα.2]
  have HE : |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ |T| * (23 / α) := by
    rw [abs_mul]; gcongr
  have HRad : |2 * R / H - (R ^ 2 - 4 + T) * L / H ^ 2| ≤ 450 / α ^ 2 := by
    calc
      _ ≤ |2 * R / H| + |(R ^ 2 - 4 + T) * L / H ^ 2| := abs_sub _ _
      _ = 2 * R / H + |R ^ 2 - 4 + T| * |L| / H ^ 2 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * R / H), abs_div, abs_mul,
          abs_of_nonneg (sq_nonneg H)]
      _ ≤ 2 * 5 / α ^ 2 + (22 * α) * (20 * α) / (α ^ 2) ^ 2 := by gcongr
      _ = 450 / α ^ 2 := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ K * (23 / α) := HE.trans (mul_le_mul_of_nonneg_right hK (by positivity))
      _ = _ := by ring
  · calc
      _ ≤ (α ^ 2 / 1000) * (23 / α) := HE.trans (mul_le_mul_of_nonneg_right hT (by positivity))
      _ = _ := by field_simp
  · calc
      _ ≤ K * (450 / α ^ 2) := by rw [abs_mul]; exact mul_le_mul hK HRad (abs_nonneg _) hK0
      _ = _ := by ring
  · have HN' : |R ^ 2 - 4 + 2 * T| ≤ 23 * α := by
      have H := abs_add_le (R ^ 2 - 4 + T) T
      have Heq : R ^ 2 - 4 + 2 * T = (R ^ 2 - 4 + T) + T := by ring
      rw [Heq]
      nlinarith only [H, hN, hT, hα.1, hα.2]
    calc
      _ ≤ 1 + |R ^ 2 - 4 + 2 * T| / H := by
        have Ha : |1 + (R ^ 2 - 4 + 2 * T) / H| ≤ |(1 : ℝ)| + |(R ^ 2 - 4 + 2 * T) / H| := abs_add_le _ _
        simpa only [abs_one, abs_div, abs_of_pos hH0] using Ha
      _ ≤ 1 + 23 * α / α ^ 2 := by gcongr
      _ ≤ 24 / α := by
        apply (le_div_iff₀ hα0).mpr
        field_simp
        nlinarith only [hα.2]
