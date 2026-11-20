-- Prove2me | solution 1 for BooleanFun.dderiv_walsh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:10:35.098331+00:00
-- url     : https://prove2.me/submissions/330ae5c7-31e2-4a02-a219-9fb5bccca7b1

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_walsh_setAt_eq_ite

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (i : Fin n) (S : Finset (Fin n)) : dderiv i (χ S) = ite (i ∈ S) (χ (S \ {i})) 0 := by
  funext
  simp [dderiv]
  repeat rw [walsh_setAt_eq_ite]
  split_ifs <;> simp
end BooleanFun
