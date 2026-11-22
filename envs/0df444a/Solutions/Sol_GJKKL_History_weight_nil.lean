-- Prove2me | solution 1 for GJKKL.History.weight_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:05.894809+00:00
-- url     : https://prove2.me/submissions/eaf7027d-e6c3-4d1b-ab43-f64dd451add2

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
theorem _root_.solution : weight κ [] = 1 := rfl
end GJKKL.History
