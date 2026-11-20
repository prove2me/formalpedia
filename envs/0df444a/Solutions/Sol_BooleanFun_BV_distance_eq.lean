-- Prove2me | solution 1 for BooleanFun.BV.distance_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:57.859568+00:00
-- url     : https://prove2.me/submissions/d9a0a7bf-5a18-428e-821a-33f77a3c1898

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_BV_oneOn_ne_of_one_or_neg_one

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) (hbvg : BooleanValued g) :
    distance f g = 𝐄 (fun x ↦ (1/2) * (1-(f x) * (g x))) := by
  simp_rw [distance, oneOn_ne_of_one_or_neg_one (hbv.one_or_neg_one _) (hbvg.one_or_neg_one _)]
end BooleanFun.BV
