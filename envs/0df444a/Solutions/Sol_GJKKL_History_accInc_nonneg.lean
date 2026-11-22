-- Prove2me | solution 1 for GJKKL.History.accInc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:26:36.269325+00:00
-- url     : https://prove2.me/submissions/3fd09b76-1f0c-4c51-ae4d-12f602d25e13

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_condAbsInc_nonneg
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
theorem _root_.solution : ∀ h : List α, 0 ≤ accInc κ X G h
  | [] => le_rfl
  | a :: h => by
    have := solution h
    simp only [accInc]
    split_ifs
    · linarith [condAbsInc_nonneg κ X h]
    · exact this
end GJKKL.History
