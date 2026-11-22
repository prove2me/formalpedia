-- Prove2me | solution 1 for GJKKL.History.accInc_cons_of_not_alive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:38.704799+00:00
-- url     : https://prove2.me/submissions/32c283ab-d48c-4f4c-a76e-615c464949b3

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
theorem _root_.solution {a : α} {h : List α} (hal : ¬ AliveBefore G (a :: h)) :
    accInc κ X G (a :: h) = accInc κ X G h := by
  simp only [accInc, if_neg hal]
end GJKKL.History
