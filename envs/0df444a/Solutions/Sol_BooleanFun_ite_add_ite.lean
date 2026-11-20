-- Prove2me | solution 1 for BooleanFun.ite_add_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:24.487322+00:00
-- url     : https://prove2.me/submissions/a17e56cc-1364-48ca-a613-872d59a043b7

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
theorem _root_.solution {α : Type*} [AddCommMonoid α] (a₁ b₁ a₂ b₂ : α):
    ite P a₁ b₁ + ite P a₂ b₂ = ite P (a₁ + a₂) (b₁ + b₂) := by split_ifs <;> simp
end BooleanFun
