-- Prove2me | solution 1 for F6ConvexWindow.degree_sum_eq_twice_A2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:53:19.81608+00:00
-- url     : https://prove2.me/submissions/c1c46810-b2fc-4fe2-8ae0-e6bff8283a3f

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_degree_pair_fiber
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal
attribute [local simp] F6ConvexWindow.mem_antichains

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution : (∑ x : V, (Inc x).card) = 2 * Ak (V := V) 2 := by
  classical
  let F := (antichains (V := V)).filter (fun T => T.card = 2)
  calc
    (∑ x : V, (Inc x).card) = ∑ x : V, (F.filter (fun T => x ∈ T)).card := by
      apply sum_congr rfl
      intro x hx
      exact degree_pair_fiber x
    _ = ∑ T ∈ F, ∑ x : V, if x ∈ T then 1 else 0 := by
      simp only [card_filter]
      rw [sum_comm]
    _ = ∑ T ∈ F, T.card := by simp
    _ = ∑ T ∈ F, 2 := by
      apply sum_congr rfl
      intro T hT
      exact (mem_filter.mp hT).2
    _ = 2 * Ak (V := V) 2 := by simp [Ak, F, Nat.mul_comm]
end F6ConvexWindow
