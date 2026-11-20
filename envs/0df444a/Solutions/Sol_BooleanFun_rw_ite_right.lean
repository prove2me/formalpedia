-- Prove2me | solution 1 for BooleanFun.rw_ite_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:13.373446+00:00
-- url     : https://prove2.me/submissions/2290e34d-c9d0-47e2-ad1f-6f6813c0f7c8

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary

set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
variable {α : Sort*} {P : Prop} [Decidable P] {a b c : α}
namespace BooleanFun
theorem _root_.solution (h : ¬P → a = c):
    ite P b a = ite P b c := by split_ifs; rfl; rw [h]; assumption
end BooleanFun
