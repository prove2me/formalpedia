-- Prove2me | solution 1 for BooleanFun.BV.eq_one_or_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:05.078803+00:00
-- url     : https://prove2.me/submissions/7128f733-0b15-4d7a-b695-3e047c8858a5

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) : ∀ x, f x = 1 ∨ f x = -1 :=
  hbv.one_or_neg_one
end BooleanFun.BV
