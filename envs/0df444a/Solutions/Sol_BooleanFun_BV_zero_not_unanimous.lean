-- Prove2me | solution 1 for BooleanFun.BV.zero_not_unanimous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:50.591146+00:00
-- url     : https://prove2.me/submissions/33e32192-062c-4547-b06c-66bf923bbf7c

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow

set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
namespace BooleanFun.BV
theorem _root_.solution (f : BooleanFunc n) (hn : n = 0) : ¬IsUnanimous f := by
  rw [IsUnanimous]
  push Not
  intro h
  have : (1 : Fin n → Fin 2) = 0 := by
    rw [hn]; trivial
  rw [this, h]
  norm_num
end BooleanFun.BV
