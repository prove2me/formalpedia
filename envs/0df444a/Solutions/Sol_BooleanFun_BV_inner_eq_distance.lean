-- Prove2me | solution 1 for BooleanFun.BV.inner_eq_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:42.843836+00:00
-- url     : https://prove2.me/submissions/5a8796bb-6597-465d-89dc-6f9266b1a4fd

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_BV_distance_eq

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) (hbvg : BooleanValued g) :
    ⟪f, g⟫ = 1-2 * distance f g := by
  rw [distance_eq hbv hbvg, expectation]
  dsimp
  rw [← mul_sum, sum_sub_distrib]
  ring_nf
  simp
  rw [mul_comm, ← inv_pow, ← one_div]
  rfl
end BooleanFun.BV
