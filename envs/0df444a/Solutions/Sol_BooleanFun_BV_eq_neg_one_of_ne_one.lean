-- Prove2me | solution 1 for BooleanFun.BV.eq_neg_one_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:10:53.568162+00:00
-- url     : https://prove2.me/submissions/e188bc11-cadc-4aa3-8ced-e2bfcdc2f33f

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) (h' : f x ≠ 1) : f x = -1 :=
  or_iff_not_imp_left.mp (hbv.one_or_neg_one x) h'
end BooleanFun.BV
