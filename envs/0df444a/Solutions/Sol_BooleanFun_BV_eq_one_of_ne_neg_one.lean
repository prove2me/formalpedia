-- Prove2me | solution 1 for BooleanFun.BV.eq_one_of_ne_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:07.95518+00:00
-- url     : https://prove2.me/submissions/b0e7c36b-7f78-4a34-bb6c-84c720f8707b

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) (h' : f x ≠ -1) : f x = 1 :=
  or_iff_not_imp_right.mp (hbv.one_or_neg_one x) h'
end BooleanFun.BV
