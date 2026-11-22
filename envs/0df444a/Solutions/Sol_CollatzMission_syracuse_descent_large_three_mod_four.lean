-- Prove2me | solution 1 for CollatzMission.syracuse_descent_large_three_mod_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-22T16:53:33.357805+00:00
-- url     : https://prove2.me/submissions/2ade8fea-1f62-4f45-8c19-b45c6723d3f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_syracuse_descent_seven_mod_thirtytwo
import Theorems.Thm_syracuse_descent_twentyseven_mod_thirtytwo
import Theorems.Thm_syracuse_descent_fifteen_mod_sixteen
import Theorems.Thm_CollatzFrontier_syracuse_terminal_budget_of_descent

set_option autoImplicit false

namespace LargeThreeModFour

/-- Parity of the second residue of the eleven-branch: `17` for `i = 0`, `13` for `i = 1`. -/
theorem odd_eleven (i : ℕ) (hi : i < 2) :
    Odd (if i + 1 = 0 then 11 else if i + 1 = 1 then 17 else 13) := by
  interval_cases i
  · refine ⟨8, by norm_num⟩
  · refine ⟨6, by norm_num⟩

/-- Parity of the second residue of the twentythree-branch: `35` for `i = 0`, `53` for `i = 1`. -/
theorem odd_twentythree (i : ℕ) (hi : i < 2) :
    Odd (if i + 1 = 0 then 23 else if i + 1 = 1 then 35 else 53) := by
  interval_cases i
  · refine ⟨17, by norm_num⟩
  · refine ⟨26, by norm_num⟩

/-- The class `n ≡ 3 mod 32`: the trajectory `3 ↦ 5` ends in the truncated terminal row
`3 * 5 + 1 = 2 ^ 4 * 1` with quotient `1 < 3`, so two steps descend on the whole class. -/
theorem class_thre (n : ℕ) (h : n % 32 = 3) : ∃ t : ℕ, syracuseStep^[t] n < n := by
  have hn : n = 3 + 2 ^ 5 * (n / 32) := by omega
  refine ⟨2, ?_⟩
  rw [hn]
  exact CollatzFrontier.syracuse_terminal_budget_of_descent
    (fun _ => 1) (fun i => 3 + 2 * i) 3 5 1 4 1 rfl
    (by intro i hi; interval_cases i <;> norm_num)
    (by intro i hi; refine ⟨i + 2, by ring⟩)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (n / 32)

/-- The class `n ≡ 11 mod 32`: rows `11 ↦ 17 ↦ 13`, then the truncated terminal row
`3 * 13 + 1 = 2 ^ 2 * 10` with quotient `10 < 11`; three steps descend. -/
theorem class_eleven (n : ℕ) (h : n % 32 = 11) : ∃ t : ℕ, syracuseStep^[t] n < n := by
  have hn : n = 11 + 2 ^ 5 * (n / 32) := by omega
  refine ⟨3, ?_⟩
  rw [hn]
  exact CollatzFrontier.syracuse_terminal_budget_of_descent
    (fun i => if i = 0 then 1 else 2)
    (fun i => if i = 0 then 11 else if i = 1 then 17 else 13)
    11 5 2 2 10 rfl
    (by intro i hi; interval_cases i <;> norm_num)
    (by intro i hi; exact odd_eleven i hi)
    (by norm_num)
    (by
      rw [Finset.sum_range_succ']
      rw [Finset.sum_range_succ']
      norm_num)
    (by norm_num)
    (n / 32)

/-- The class `n ≡ 19 mod 32`: rows `19 ↦ 29`, then the terminal row `3 * 29 + 1 = 2 ^ 3 * 11`
with quotient `11 < 19`; two steps descend. -/
theorem class_nineteen (n : ℕ) (h : n % 32 = 19) : ∃ t : ℕ, syracuseStep^[t] n < n := by
  have hn : n = 19 + 2 ^ 5 * (n / 32) := by omega
  refine ⟨2, ?_⟩
  rw [hn]
  exact CollatzFrontier.syracuse_terminal_budget_of_descent
    (fun _ => 1) (fun i => 19 + 10 * i) 19 5 1 3 11 rfl
    (by intro i hi; interval_cases i <;> norm_num)
    (by intro i hi; refine ⟨5 * i + 14, by ring⟩)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (n / 32)

/-- The class `n ≡ 23 mod 32`: rows `23 ↦ 35 ↦ 53`, then the truncated terminal row
`3 * 53 + 1 = 2 ^ 3 * 20` with quotient `20 < 23`; three steps descend. -/
theorem class_twentythree (n : ℕ) (h : n % 32 = 23) : ∃ t : ℕ, syracuseStep^[t] n < n := by
  have hn : n = 23 + 2 ^ 5 * (n / 32) := by omega
  refine ⟨3, ?_⟩
  rw [hn]
  exact CollatzFrontier.syracuse_terminal_budget_of_descent
    (fun _ => 1)
    (fun i => if i = 0 then 23 else if i = 1 then 35 else 53)
    23 5 2 3 20 rfl
    (by intro i hi; interval_cases i <;> norm_num)
    (by intro i hi; exact odd_twentythree i hi)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (n / 32)

end LargeThreeModFour

theorem solution (n : ℕ) (hn : 2310000 ≤ n) (hmod : n % 4 = 3) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  have h32 : n % 32 = 3 ∨ n % 32 = 7 ∨ n % 32 = 11 ∨ n % 32 = 15 ∨
             n % 32 = 19 ∨ n % 32 = 23 ∨ n % 32 = 27 ∨ n % 32 = 31 := by omega
  rcases h32 with h32 | h32 | h32 | h32 | h32 | h32 | h32 | h32
  · exact LargeThreeModFour.class_thre n h32
  · exact syracuse_descent_seven_mod_thirtytwo n h32
  · exact LargeThreeModFour.class_eleven n h32
  · exact syracuse_descent_fifteen_mod_sixteen n (by omega)
  · exact LargeThreeModFour.class_nineteen n h32
  · exact LargeThreeModFour.class_twentythree n h32
  · exact syracuse_descent_twentyseven_mod_thirtytwo n h32
  · exact syracuse_descent_fifteen_mod_sixteen n (by omega)
