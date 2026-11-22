-- Prove2me | solution 1 for GJKKL.History.prob_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:47.662641+00:00
-- url     : https://prove2.me/submissions/59b446dc-a575-409a-af3d-661bf6682da2

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_expect_mono
public import Theorems.Thm_GJKKL_History_expect_sum

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution {ι : Type*} (s : Finset ι) (T : ℕ) (P : ι → List α → Prop) :
    prob κ T (fun h => ∃ i ∈ s, P i h) ≤ ∑ i ∈ s, prob κ T (P i) := by
  classical
  unfold prob
  rw [← expect_sum]
  refine expect_mono κ fun h _ => ?_
  split_ifs with hex
  · obtain ⟨i, hi, hPi⟩ := hex
    calc (1 : ℝ) = if P i h then 1 else 0 := by rw [if_pos hPi]
      _ ≤ ∑ j ∈ s, if P j h then 1 else 0 :=
        single_le_sum (f := fun j => if P j h then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
  · exact sum_nonneg fun j _ => by split_ifs <;> norm_num
end GJKKL.History
