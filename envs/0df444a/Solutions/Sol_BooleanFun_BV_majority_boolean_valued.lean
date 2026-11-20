-- Prove2me | solution 1 for BooleanFun.BV.majority_boolean_valued
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:26.596441+00:00
-- url     : https://prove2.me/submissions/594a816d-5541-4e4e-9c50-6c413467fb9f

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
theorem _root_.solution : BooleanValued (@majority n) where
  one_or_neg_one := by
    intro x
    rw [majority.eq_def]
    split_ifs
    · left; rfl
    · right; rfl
end BooleanFun.BV
