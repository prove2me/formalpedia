-- Prove2me | solution 1 for GJKKL.History.condAbsInc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:23.420935+00:00
-- url     : https://prove2.me/submissions/7708e4e7-f8c9-47d8-8e92-b2fc80954f84

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α) (X : List α → ℝ) (G : List α → Prop)
namespace GJKKL.History
theorem _root_.solution (h : List α) : 0 ≤ condAbsInc κ X h :=
  sum_nonneg fun a _ => mul_nonneg (κ.nonneg h a) (abs_nonneg _)
end GJKKL.History
