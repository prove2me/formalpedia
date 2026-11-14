-- Prove2me | solution 1 for CountingLLL.ContractedWalk.running_level_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:30:52.872352+00:00
-- url     : https://prove2.me/submissions/f9bee402-bea2-4e63-99e5-69a2e753bc69

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_path_balance

set_option autoImplicit false

open CountingLLL.ContractedWalk
open scoped BigOperators

/-- At every time in the abstract contracted walk, the level is bounded by
 twice the running counter minus one. -/
theorem solution (ω : Tape) (j t : ℕ) (hj : 1 ≤ j) :
    level ω (2*j-1) t ≤
      2 * (j + ∑ k ∈ Finset.range t,
        if level ω (2*j-1) k ≠ 0 ∧ ω k = true then 1 else 0) - 1 := by
  classical
  let A := ∑ k ∈ Finset.range t, if level ω (2*j-1) k = 0 then 0 else 1
  let U := ∑ k ∈ Finset.range t, if level ω (2*j-1) k ≠ 0 ∧ ω k = true then 1 else 0
  have hAU : U ≤ A := by
    apply Finset.sum_le_sum
    intro k hk
    split_ifs <;> omega
  have hb := path_balance ω (2*j-1) t
  change level ω (2*j-1) t + A = (2*j-1) + 3*U at hb
  change level ω (2*j-1) t ≤ 2*(j+U)-1
  omega
