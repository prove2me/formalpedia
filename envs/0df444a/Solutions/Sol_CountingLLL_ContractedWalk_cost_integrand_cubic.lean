-- Prove2me | solution 1 for CountingLLL.ContractedWalk.cost_integrand_cubic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:50:55.292869+00:00
-- url     : https://prove2.me/submissions/e3ea5910-6f3d-405e-b930-1d6c91c6bf61

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_bounds
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_recursion
set_option autoImplicit false
open CountingLLL.ContractedWalk

/-- The paper's cost integrand after solving the cubic for (1-G)/(1-z). -/
theorem solution (θ z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/3)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    let g := generatingFunction θ z
    ((1-g)/(θ*(1-z))-1)/θ = z*(1+g+g^2)/(1-θ*z*(1+g+g^2)) := by
  let g := generatingFunction θ z
  have hg := generating_function_bounds θ z (by linarith) hz0 (by linarith)
  change 0 ≤ g ∧ g ≤ 1 at hg
  have hc := generating_function_recursion θ z (by linarith) hθ1 hz0 (by linarith)
  change g = 1-θ+θ*z*g^3 at hc
  have ha0 : 0 ≤ 1+g+g^2 := by nlinarith [sq_nonneg g]
  have ha1 : 1+g+g^2 ≤ 3 := by nlinarith [sq_nonneg (g-1)]
  have hz1' : 0 < 1-z := by linarith
  have hθz : 0 ≤ θ*z := by positivity
  have hh : θ*z*(1+g+g^2) ≤ 3*θ*z := by
    nlinarith [mul_nonneg hθz (sub_nonneg.mpr ha1)]
  have ht : θ*z ≤ θ := by nlinarith [mul_nonneg (le_of_lt hθ0) (sub_nonneg.mpr (le_of_lt hz1))]
  have hd : 0 < 1-θ*z*(1+g+g^2) := by linarith
  change ((1-g)/(θ*(1-z))-1)/θ = z*(1+g+g^2)/(1-θ*z*(1+g+g^2))
  field_simp [ne_of_gt hθ0, ne_of_gt hz1', ne_of_gt hd]
  nlinarith [hc]
