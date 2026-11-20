-- Prove2me | solution 1 for BooleanFun.BV.walsh_boolean_valued
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:14.716028+00:00
-- url     : https://prove2.me/submissions/a42d1262-148e-4b84-9beb-6de743b0222a

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_walsh_eq_neg_one_pow_sum


set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (S : Finset (Fin n)) : BooleanValued (χ S) where
    one_or_neg_one := by simp_rw [walsh_eq_neg_one_pow_sum, neg_one_pow_eq_or _, implies_true]
end BooleanFun.BV
