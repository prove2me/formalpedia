-- Prove2me | solution 1 for BianchiIX.terminal_amplitude_power_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:51:52.051256+00:00
-- url     : https://prove2.me/submissions/e474bebc-736a-4437-a392-512af993045a

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- The terminal phase budget absorbs both inverse fourth powers without losing the exponent 19/10. -/
theorem solution {α b A U W u v w : ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hb : 0 < b) (hbudget : b ≤ α ^ (40 : ℕ)) (hA : 1 ≤ A)
    (hU : 0 ≤ U) (hW : 0 ≤ W) (hsum : U + W ≤ b)
    (hu : 0 ≤ u ∧ u ≤ α ^ (4 : ℕ)) (hv : 0 ≤ v ∧ v ≤ A * W / α ^ 2)
    (hw : 0 ≤ w ∧ w ≤ A * U / α ^ 2) :
    u * v ^ (19 / 10 : ℝ) ≤ A ^ 2 * b ^ (19 / 10 : ℝ) ∧
      w * v ≤ A ^ 2 * b ^ (19 / 10 : ℝ) := by
  have hA0 : 0 ≤ A := by linarith
  have hUb : U ≤ b := by linarith
  have hWb : W ≤ b := by linarith
  have hscale : α ^ (4 : ℕ) / (α ^ (2 : ℕ)) ^ (19 / 10 : ℝ) = α ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast α 4, ← Real.rpow_natCast α 2, ← Real.rpow_mul hα.1.le,
      ← Real.rpow_sub hα.1]
    norm_num
  have hAexp : A ^ (19 / 10 : ℝ) ≤ A ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast A 2]
    exact Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hαexp : α ^ (1 / 5 : ℝ) ≤ 1 := Real.rpow_le_one hα.1.le hα.2 (by norm_num)
  have hbroot : b ^ (1 / 10 : ℝ) ≤ α ^ (4 : ℕ) := by
    have H := Real.rpow_le_rpow hb.le hbudget (by norm_num : (0 : ℝ) ≤ 1 / 10)
    rw [← Real.rpow_natCast α 40, ← Real.rpow_mul hα.1.le] at H
    norm_num at H
    exact H
  have hbprod : b ^ (2 : ℕ) = b ^ (19 / 10 : ℝ) * b ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hb]
    norm_num
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ α ^ (4 : ℕ) * (A * W / α ^ 2) ^ (19 / 10 : ℝ) :=
        mul_le_mul hu.2 (Real.rpow_le_rpow hv.1 hv.2 (by norm_num))
          (Real.rpow_nonneg hv.1 _) (pow_nonneg hα.1.le _)
      _ = (A ^ (19 / 10 : ℝ) * W ^ (19 / 10 : ℝ)) * α ^ (1 / 5 : ℝ) := by
        rw [Real.div_rpow (mul_nonneg hA0 hW) (sq_nonneg α), Real.mul_rpow hA0 hW]
        rw [show α ^ 4 * (A ^ (19 / 10 : ℝ) * W ^ (19 / 10 : ℝ) / (α ^ 2) ^ (19 / 10 : ℝ)) =
          (A ^ (19 / 10 : ℝ) * W ^ (19 / 10 : ℝ)) *
            (α ^ 4 / (α ^ 2) ^ (19 / 10 : ℝ)) by ring, hscale]
      _ ≤ A ^ (19 / 10 : ℝ) * W ^ (19 / 10 : ℝ) := mul_le_of_le_one_right (by positivity) hαexp
      _ ≤ _ := mul_le_mul hAexp (Real.rpow_le_rpow hW hWb (by norm_num)) (by positivity) (sq_nonneg A)
  · have Huv : U * W ≤ b ^ 2 := by nlinarith [mul_le_mul hUb hWb hW hb.le]
    have Hpow : b ^ 2 / α ^ 4 ≤ b ^ (19 / 10 : ℝ) := by
      apply (div_le_iff₀ (pow_pos hα.1 4)).mpr
      rw [hbprod]
      exact mul_le_mul_of_nonneg_left hbroot (by positivity)
    calc
      _ ≤ (A * U / α ^ 2) * (A * W / α ^ 2) := mul_le_mul hw.2 hv.2 hv.1 (by positivity)
      _ = A ^ 2 * (U * W / α ^ 4) := by ring
      _ ≤ A ^ 2 * (b ^ 2 / α ^ 4) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left Hpow (sq_nonneg A)
