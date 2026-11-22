-- Prove2me | solution 1 for GJKKL.History.weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:32.870627+00:00
-- url     : https://prove2.me/submissions/68ec8286-40bd-47a4-989e-471bb52e5e92

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
theorem _root_.solution : ∀ h : List α, 0 ≤ weight κ h
  | [] => zero_le_one
  | a :: h => mul_nonneg (solution h) (κ.nonneg h a)
end GJKKL.History
