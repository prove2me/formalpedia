-- Prove2me | solution 1 for BooleanFun.laplace_eq_dderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:10:19.901496+00:00
-- url     : https://prove2.me/submissions/846f3246-ba6a-40b6-82d5-1ce36a9c7b6d

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_setAt_eq_id
import Theorems.Thm_BooleanFun_setAt_eq_flipAt

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (i : Fin n) (f : BooleanFunc n) (x : Fin n → Fin 2):
    laplace i f x = (-1) ^ (x i).val * (dderiv i f x) := by
  change (f x - _) / 2 = (-1)^_ * ( (_ - _) / 2 )
  by_cases hx : x i = 0
  · simp [hx]
    rw [setAt_eq_id hx, setAt_eq_flipAt (by rw [hx]; trivial)]
  · have hx1 := Fin.eq_one_of_ne_zero (x i) hx
    rw [setAt_eq_id hx1, setAt_eq_flipAt hx]
    simp [hx1]; ring
end BooleanFun
