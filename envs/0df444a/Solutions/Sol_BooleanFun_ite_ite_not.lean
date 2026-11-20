-- Prove2me | solution 1 for BooleanFun.ite_ite_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:24.985063+00:00
-- url     : https://prove2.me/submissions/d0b67096-4c3c-4ee3-be21-d70a02d1888d

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
theorem _root_.solution (P : Prop) [Decidable P] (a b c : α):
    ite P (ite (¬P) a b) c = ite P b c := by split_ifs <;> rfl
end BooleanFun
