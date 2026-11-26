-- Prove2me | solution 1 for CSeparatedNPComplete.inv_one_plus_line_eq_binary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:14.883266+00:00
-- url     : https://prove2.me/submissions/d880dfb9-d641-4fa7-8175-72f86d41e9fe

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (1 + x)⁻¹ = 1 - x / 2 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have he := congrArg (fun z : ℝ => z * (1 + x)) h
    rw [inv_mul_cancel₀ (by linarith : 1 + x ≠ 0)] at he
    have hp : x * (1 - x) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num
end CSeparatedNPComplete
