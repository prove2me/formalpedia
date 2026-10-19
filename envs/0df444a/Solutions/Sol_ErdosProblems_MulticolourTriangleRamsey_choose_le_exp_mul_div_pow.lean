-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.choose_le_exp_mul_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/2d2ba1c0-9989-405a-8bb3-499249a7ae54

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_factorial_exp_lower

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (N s : ℕ) (hs : 0 < s) :
    (N.choose s : ℝ) ≤
      (Real.exp 1 * (N : ℝ) / (s : ℝ)) ^ s := by
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsmall : 0 < ((s : ℝ) / Real.exp 1) ^ s := by positivity
  calc
    (N.choose s : ℝ) ≤ (N : ℝ) ^ s / (s.factorial : ℝ) :=
      Nat.choose_le_pow_div s N
    _ ≤ (N : ℝ) ^ s / (((s : ℝ) / Real.exp 1) ^ s) :=
      div_le_div_of_nonneg_left (by positivity) hsmall
        (factorial_exp_lower s hs)
    _ = (Real.exp 1 * (N : ℝ) / (s : ℝ)) ^ s := by
      rw [← div_pow]
      congr 1
      field_simp
end ErdosProblems.MulticolourTriangleRamsey
