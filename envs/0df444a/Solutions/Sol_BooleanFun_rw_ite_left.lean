-- Prove2me | solution 1 for BooleanFun.rw_ite_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:10.613395+00:00
-- url     : https://prove2.me/submissions/f75d8077-0833-4954-a2e8-3c8a7d5c683a

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
theorem _root_.solution (h : P → a = c):
    ite P a b = ite P c b := by split_ifs; rw [h]; assumption; rfl
end BooleanFun
