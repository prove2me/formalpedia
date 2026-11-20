-- Prove2me | solution 1 for BooleanFun.oneOn_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:00:03.866645+00:00
-- url     : https://prove2.me/submissions/3be95006-e79f-4055-8f50-e05674de0b60

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
noncomputable section
variable {p q : Prop}
open Classical
namespace BooleanFun
theorem _root_.solution : oneOn (¬p) = 1 - oneOn p := by
  unfold oneOn; split_ifs <;> simp
end BooleanFun
