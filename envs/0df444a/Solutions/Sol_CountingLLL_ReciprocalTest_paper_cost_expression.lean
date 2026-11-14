-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.paper_cost_expression
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:19:46.234544+00:00
-- url     : https://prove2.me/submissions/b4881fd3-a712-442a-83fe-700c7467a633

import Definitions.Def_CountingLLL_ContractedCost
import Theorems.Thm_CountingLLL_ReciprocalTest_source_parameter_bounds
import Theorems.Thm_CountingLLL_ReciprocalTest_paper_oracle_cost_scalar_bound
import Theorems.Thm_CountingLLL_ContractedWalk_source_M_bound
set_option autoImplicit false
open CountingLLL.ContractedWalk CountingLLL.ReciprocalTest
open scoped ENNReal

theorem solution (B : ℝ) (hB : Real.exp (-(3/10 : ℝ)) ≤ B) (hB1 : B ≤ 1) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let M := (expectedWeightedChanges (ENNReal.ofReal θ) 3 2).toReal
    1-u+(1-u^2)/(1-u+u^2) * (1-u+u/(1-u+u^2)*M) < 3 := by
  let u : ℝ := 2*(1-B)/(2-B)
  let θ : ℝ := u^2/(1-u+u^2)
  let M : ℝ := (expectedWeightedChanges (ENNReal.ofReal θ) 3 2).toReal
  have huθ := source_parameter_bounds B hB hB1
  change 0 ≤ u ∧ u < 33/80 ∧ 0 ≤ θ ∧ θ < 9/40 at huθ
  have hbound := source_M_bound θ huθ.2.2.1 (by linarith [huθ.2.2.2])
  have hfinite : expectedWeightedChanges (ENNReal.ofReal θ) 3 2 ≠ ⊤ := by
    exact ne_of_lt (lt_trans hbound ENNReal.ofReal_lt_top)
  have hM : M ≤ 74/25 := by
    have hh := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hbound
    change M < (ENNReal.ofReal (74/25 : ℝ)).toReal at hh
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 74/25)] at hh
    linarith
  exact paper_oracle_cost_scalar_bound u M huθ.1 (by linarith [huθ.2.1]) ENNReal.toReal_nonneg hM
