-- Prove2me | solution 1 for CountingLLL.ContractedWalk.path_balance
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:27:05.052539+00:00
-- url     : https://prove2.me/submissions/8c66bdfb-45b2-4f9c-8611-fa9124275425

import Definitions.Def_CountingLLL_ContractedWalk
set_option autoImplicit false
open CountingLLL.ContractedWalk
open scoped BigOperators

theorem solution (ω : Tape) (i t : ℕ) :
    level ω i t + (∑ k ∈ Finset.range t, if level ω i k = 0 then 0 else 1) =
      i + 3*(∑ k ∈ Finset.range t, if level ω i k ≠ 0 ∧ ω k = true then 1 else 0) := by
  induction t with
  | zero => simp [level]
  | succ t ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [level]
    split <;> split <;> simp_all <;> omega
