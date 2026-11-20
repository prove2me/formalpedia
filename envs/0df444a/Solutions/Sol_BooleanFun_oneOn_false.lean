-- Prove2me | solution 1 for BooleanFun.oneOn_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:59.557993+00:00
-- url     : https://prove2.me/submissions/f55447d0-db9b-46ec-ae4f-64136dba2916

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
theorem _root_.solution (h : ¬p) : oneOn p = 0 := by simpa
end BooleanFun
