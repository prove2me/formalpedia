-- Prove2me | solution 1 for BlockCycleRotation.muCost_antitone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:13:30.749944+00:00
-- url     : https://prove2.me/submissions/5c6a16cf-c722-4d56-a190-793b95e8dd26

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_psiBuf_antitone
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
/-- **Corollary, item 1: `μ` decreases in the buffer size.** -/
theorem solution {N l b₁ b₂ : ℝ} (hN : 0 < N) (hb : 0 < b₁) (h12 : b₁ ≤ b₂)
    (hl0 : 0 ≤ l) (hl : 2 * l ≤ N) : muCost N l b₂ ≤ muCost N l b₁:= by
  have hx0 : 0 ≤ l / N := by positivity
  have hx : l / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hbN : 0 < b₁ / N := by positivity
  have h12' : b₁ / N ≤ b₂ / N := by gcongr
  unfold muCost
  have := psiBuf_antitone h12' hbN hx0 hx
  nlinarith
