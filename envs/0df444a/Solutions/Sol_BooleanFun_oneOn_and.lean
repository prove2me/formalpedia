-- Prove2me | solution 1 for BooleanFun.oneOn_and
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:00:00.901115+00:00
-- url     : https://prove2.me/submissions/f2651758-286d-4755-869d-0009fbeb5d25

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
theorem _root_.solution : oneOn (p ∧ q) = (oneOn p) * (oneOn q) := by
  unfold oneOn; split_ifs <;> {simp; try tauto}
end BooleanFun
