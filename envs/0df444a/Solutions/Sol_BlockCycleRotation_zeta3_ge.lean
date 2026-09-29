-- Prove2me | solution 1 for BlockCycleRotation.zeta3_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:40:33.37181+00:00
-- url     : https://prove2.me/submissions/b6bfd204-ad62-4190-97e8-11bf934fa5ed

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open Real Finset Filter Topology

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
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem uTerm_pos (d : ℕ) : 0 < uTerm d := by
  unfold uTerm; positivity

theorem uTerm_summable : Summable uTerm := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine ((summable_nat_add_iff 1).2 h).congr fun d => ?_
  unfold uTerm
  push_cast
  ring

theorem tsum_uTerm : ∑' d, uTerm d = zeta3 := rfl

end BlockCycleRotation

open BlockCycleRotation in
set_option maxHeartbeats 1000000 in
/-- `ζ(3) ≥ ∑_{d ≤ 50} 1/d³ ≥ 1.2018`. -/
theorem solution : (6009 : ℝ) / 5000 ≤ zeta3:= by
  have h : ∑ d ∈ Finset.range 50, uTerm d ≤ zeta3 := by
    rw [← tsum_uTerm]
    exact uTerm_summable.sum_le_tsum _ (fun d _ => (uTerm_pos d).le)
  refine le_trans ?_ h
  norm_num [uTerm, Finset.sum_range_succ]
