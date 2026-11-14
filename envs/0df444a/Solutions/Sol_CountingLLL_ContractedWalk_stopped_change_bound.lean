-- Prove2me | solution 1 for CountingLLL.ContractedWalk.stopped_change_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:28:42.418751+00:00
-- url     : https://prove2.me/submissions/d62dca95-73aa-4e2a-9263-f2ad01c13d8d

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_path_balance

set_option autoImplicit false

open CountingLLL.ContractedWalk
open scoped BigOperators

/-- At the first absorption time, changes equal the starting level plus three
 times the number of upward changes. -/
private theorem stopTime_eq_start_add_three_increases (ω : Tape) (i : ℕ)
    (h : ∃ t, level ω i t = 0) :
    stopTime ω i = i + 3 * upwardCount ω i := by
  classical
  have hstop : stopTime ω i = Nat.find h := by simp [stopTime, h]
  have hz : level ω i (stopTime ω i) = 0 := by rw [hstop]; exact Nat.find_spec h
  have hn (k : ℕ) (hk : k < stopTime ω i) : level ω i k ≠ 0 := by
    rw [hstop] at hk
    exact Nat.find_min h hk
  have hsum : (∑ k ∈ Finset.range (stopTime ω i), if level ω i k = 0 then 0 else 1) = stopTime ω i := by
    rw [Finset.sum_congr rfl (fun k hk => if_neg (hn k (Finset.mem_range.mp hk)))]
    simp
  have hb := path_balance ω i (stopTime ω i)
  rw [hz, zero_add, hsum] at hb
  exact hb

/-- A suppressed-return walk initialized at level `2*j-1` uses at most
 three changes per final counter value. -/
theorem solution (ω : Tape) (j : ℕ) (hj : 1 ≤ j)
    (h : ∃ t, level ω (2*j-1) t = 0) :
    stopTime ω (2*j-1) ≤ 3 * (j + upwardCount ω (2*j-1)) := by
  rw [stopTime_eq_start_add_three_increases ω (2*j-1) h]
  omega
