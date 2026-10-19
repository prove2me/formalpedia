-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.factorial_exp_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/c9aaaaa9-336a-4439-940c-a39c9041b018

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (s : ℕ) (hs : 0 < s) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by
  have hsreal : (1 : ℝ) ≤ s := by
    exact_mod_cast hs
  have hradicand : (1 : ℝ) ≤ 2 * Real.pi * (s : ℝ) := by
    nlinarith [Real.pi_gt_three]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (s : ℝ)) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.pi * (s : ℝ) by positivity),
      Real.sqrt_nonneg (2 * Real.pi * (s : ℝ))]
  have hpower : 0 ≤ ((s : ℝ) / Real.exp 1) ^ s := by positivity
  calc
    ((s : ℝ) / Real.exp 1) ^ s ≤
        Real.sqrt (2 * Real.pi * (s : ℝ)) *
          ((s : ℝ) / Real.exp 1) ^ s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hpower]
    _ ≤ (s.factorial : ℝ) := Stirling.le_factorial_stirling s
end ErdosProblems.MulticolourTriangleRamsey
