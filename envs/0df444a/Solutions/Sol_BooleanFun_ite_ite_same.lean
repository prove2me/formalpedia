-- Prove2me | solution 1 for BooleanFun.ite_ite_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:10.103179+00:00
-- url     : https://prove2.me/submissions/5d283d45-39f2-446d-9bdb-31d60f9b0425

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
theorem _root_.solution (a b c : α):
    ite P (ite P a b) c = ite P a c := by split_ifs <;> rfl
end BooleanFun
