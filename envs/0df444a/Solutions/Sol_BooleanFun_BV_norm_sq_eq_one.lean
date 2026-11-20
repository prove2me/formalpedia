-- Prove2me | solution 1 for BooleanFun.BV.norm_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:05:02.704594+00:00
-- url     : https://prove2.me/submissions/f746679c-85be-4892-a0ea-fa931c1b4398

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f):
    ‖f‖^2 = 1 := by
  change √(𝐄 _) ^ 2 = 1
  conv in f * f =>
    ext x
    dsimp
    tactic =>
      have : f x * f x = 1 := by
        cases hbv.one_or_neg_one x with | _ => simp [*]
    rw [this]
  simp [expectation]
end BooleanFun.BV
