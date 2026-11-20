-- Prove2me | solution 1 for BooleanFun.setAt_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:09:05.313562+00:00
-- url     : https://prove2.me/submissions/d466b74b-70e4-4340-af7b-22c0825b1fc0

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (h : x i = v) : setAt i v x = x := by
  funext j
  unfold setAt
  split_ifs with hj
  · rw [hj]; symm; assumption
  · rfl
end BooleanFun
