-- Prove2me | solution 1 for GJKKL.History.accInc_add_of_alive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:23.137284+00:00
-- url     : https://prove2.me/submissions/d51cc939-2e77-4744-b093-b46591fe78cd

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
theorem _root_.solution : ∀ {h : List α}, AliveBefore G h → G h →
    accInc κ X G h + condAbsInc κ X h = accSum κ X h
  | [], _, _ => by simp [accInc, accSum]
  | a :: h, hal, hG => by
    have hal' : AliveBefore G (a :: h) := hal
    simp only [accInc, if_pos hal', accSum]
    rw [solution hal.1 hal.2]
end GJKKL.History
