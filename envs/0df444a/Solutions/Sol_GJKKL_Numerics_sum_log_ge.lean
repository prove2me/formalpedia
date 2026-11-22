-- Prove2me | solution 1 for GJKKL.Numerics.sum_log_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:49.24507+00:00
-- url     : https://prove2.me/submissions/9a9c99d7-372a-4c74-8244-1c2508da026e

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
public import Theorems.Thm_GJKKL_Numerics_tangent_step

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real
namespace GJKKL.Numerics
theorem _root_.solution (a : ℝ) (ha : 0 < a) :
    ∀ m : ℕ, (m : ℝ) ≤ a →
      -(a - m) * log ((a - m) / a) - m ≤ ∑ i ∈ range m, log ((a - i) / a)
  | 0, _ => by simp
  | m + 1, hm => by
    have ih := solution a ha m (by push_cast at hm; linarith)
    rw [sum_range_succ]
    have hstep := tangent_step ha (u := a - m) (by push_cast at hm; linarith)
    push_cast
    have : a - (m + 1 : ℝ) = a - m - 1 := by ring
    rw [this]
    nlinarith
end GJKKL.Numerics
