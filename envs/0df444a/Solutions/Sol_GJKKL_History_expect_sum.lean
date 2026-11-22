-- Prove2me | solution 1 for GJKKL.History.expect_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:39.076803+00:00
-- url     : https://prove2.me/submissions/fd8c9407-fa41-401b-ab33-0b4711942515

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution {ι : Type*} (s : Finset ι) (T : ℕ) (f : ι → List α → ℝ) :
    expect κ T (fun h => ∑ i ∈ s, f i h) = ∑ i ∈ s, expect κ T (f i) := by
  unfold expect
  simp_rw [mul_sum]
  rw [sum_comm]
end GJKKL.History
