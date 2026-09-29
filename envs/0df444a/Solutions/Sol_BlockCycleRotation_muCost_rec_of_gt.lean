-- Prove2me | solution 1 for BlockCycleRotation.muCost_rec_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:12:29.852605+00:00
-- url     : https://prove2.me/submissions/1ac7e500-1abc-4e3f-9f67-f277250ed2cf

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_psiBuf_rec
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

theorem Outt_pos {x : ℝ} (hx : 0 < x) : 0 < Outt x := by
  unfold Outt
  rw [if_neg (ne_of_gt hx)]
  have : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
  positivity

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
theorem solution {N l b : ℝ} (hN : 0 < N) (hb : 0 < b) (h : b < l)
    (hl : 2 * l ≤ N) :
    muCost N l b - N
      = 2 * l + (muCost (N * Outt (l / N)) (N * Outt (l / N) * Inn (l / N)) b
          - N * Outt (l / N)):= by
  have hx0 : 0 < l / N := by
    have : 0 < l := lt_trans hb h
    positivity
  have hx : l / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hbx : b / N < l / N := by gcongr
  have hbN : 0 < b / N := by positivity
  have hOut : 0 < Outt (l / N) := Outt_pos hx0
  have hN' : 0 < N * Outt (l / N) := by positivity
  unfold muCost
  rw [psiBuf_rec hbN hbx hx]
  have h1 : N * Outt (l / N) * Inn (l / N) / (N * Outt (l / N)) = Inn (l / N) := by
    field_simp
  have h2 : b / (N * Outt (l / N)) = b / N / Outt (l / N) := by
    field_simp
  rw [h1, h2]
  field_simp
  ring
