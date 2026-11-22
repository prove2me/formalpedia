-- Prove2me | solution 1 for GJKKL.History.stopped_of_alive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:26.25865+00:00
-- url     : https://prove2.me/submissions/9b05547e-62e4-49b9-86f8-b7ed09001820

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil


attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.aliveBefore_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α) (X : List α → ℝ) (G : List α → Prop)
namespace GJKKL.History
theorem _root_.solution : ∀ {h : List α}, AliveBefore G h → stopped X G h = X h
  | [], _ => rfl
  | a :: h, hal => by simp only [stopped, if_pos hal]
end GJKKL.History
