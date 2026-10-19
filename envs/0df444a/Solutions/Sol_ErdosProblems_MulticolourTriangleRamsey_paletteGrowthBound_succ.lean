-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteGrowthBound_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/00388893-067f-4277-a3aa-9bd397d221ba

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {a s j n B : ℕ}
    (hstage : ((j + 1 : ℕ) : ℝ) ^ (a * s) ≤
      (B : ℝ) * (s : ℝ) *
        (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ)) ^ s)
    (hprevious : PaletteGrowthBound a s j n) :
    PaletteGrowthBound a s (j + 1) (B * n) := by
  unfold PaletteGrowthBound at hprevious ⊢
  calc
    (((j + 1).factorial : ℕ) : ℝ) ^ (a * s) =
        ((j + 1 : ℕ) : ℝ) ^ (a * s) *
          (j.factorial : ℝ) ^ (a * s) := by
      simp [Nat.factorial_succ, mul_pow]
    _ ≤
        ((B : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 *
            ((j + 1 : ℕ) : ℝ)) ^ s) *
        ((n : ℝ) * (s : ℝ) ^ j *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * j) *
          (j.factorial : ℝ) ^ s) := by
      exact mul_le_mul hstage hprevious (by positivity) (by positivity)
    _ =
        ((B * n : ℕ) : ℝ) * (s : ℝ) ^ (j + 1) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * (j + 1)) *
          (((j + 1).factorial : ℕ) : ℝ) ^ s := by
      push_cast
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.mul_succ, pow_add, pow_succ, mul_pow]
      ring
end ErdosProblems.MulticolourTriangleRamsey
