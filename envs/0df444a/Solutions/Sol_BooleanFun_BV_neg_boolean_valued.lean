-- Prove2me | solution 1 for BooleanFun.BV.neg_boolean_valued
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:11.734291+00:00
-- url     : https://prove2.me/submissions/32da4e38-967a-4394-b16d-f454317c19cf

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) : BooleanValued (-f) where
  one_or_neg_one := by intro x; rw [Pi.neg_apply, neg_inj, neg_eq_iff_eq_neg, or_comm]; exact hbv.one_or_neg_one _
end BooleanFun.BV
