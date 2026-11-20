-- Prove2me | solution 1 for BooleanFun.BV.fourier_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:06:32.804226+00:00
-- url     : https://prove2.me/submissions/d7e2116a-2c2d-4160-a4f4-fec85e6192c0

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_BV_norm_sq_eq_one
import Theorems.Thm_BooleanFun_walsh_plancherel


set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) : ∑ S, |𝓕 f S|^2 = 1 := by
  rw [← walsh_plancherel]
  exact norm_sq_eq_one hbv
end BooleanFun.BV
