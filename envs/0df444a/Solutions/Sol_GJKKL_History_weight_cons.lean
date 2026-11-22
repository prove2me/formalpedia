-- Prove2me | solution 1 for GJKKL.History.weight_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:05.503818+00:00
-- url     : https://prove2.me/submissions/d1944f13-0286-4c44-8bc3-d46c27646134

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
theorem _root_.solution (a : α) (h : List α) : weight κ (a :: h) = weight κ h * κ.K h a :=
  rfl
end GJKKL.History
