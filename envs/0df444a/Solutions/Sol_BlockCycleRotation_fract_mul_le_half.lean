-- Prove2me | solution 1 for BlockCycleRotation.fract_mul_le_half
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:08:06.015553+00:00
-- url     : https://prove2.me/submissions/70e3e579-81a3-4f18-a4fb-7ddd6763b16f

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **`g·{1/g} ≤ 1/2`** for `0 ≤ g < 1`. -/
theorem solution {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    g * Int.fract (1 / g) ≤ 1 / 2:= by
  rcases eq_or_lt_of_le hg0 with h | hg
  · rw [← h]; simp
  · have hm : (1 : ℝ) < 1 / g := by rw [lt_div_iff₀ hg]; linarith
    have hm1 : (1 : ℝ) ≤ ((⌊1 / g⌋ : ℤ) : ℝ) := by
      have : (1 : ℤ) ≤ ⌊1 / g⌋ := Int.le_floor.2 (by exact_mod_cast le_of_lt hm)
      exact_mod_cast this
    have hlt : 1 / g < ((⌊1 / g⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hub : 1 < (((⌊1 / g⌋ : ℤ) : ℝ) + 1) * g := (div_lt_iff₀ hg).1 hlt
    rw [Int.fract]
    have heq : g * (1 / g - ((⌊1 / g⌋ : ℤ) : ℝ)) = 1 - g * ((⌊1 / g⌋ : ℤ) : ℝ) := by
      field_simp
    rw [heq]
    nlinarith [hub, hm1, hg,
      mul_lt_mul_of_pos_left hub (show (0 : ℝ) < ((⌊1 / g⌋ : ℤ) : ℝ) by linarith)]
