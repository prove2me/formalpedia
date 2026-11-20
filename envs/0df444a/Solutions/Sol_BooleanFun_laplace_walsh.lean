-- Prove2me | solution 1 for BooleanFun.laplace_walsh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:16.532927+00:00
-- url     : https://prove2.me/submissions/4479e5e1-89f8-4cf8-a428-80c7b9b9d644

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_dderiv_walsh
import Theorems.Thm_BooleanFun_laplace_eq_dderiv

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (i : Fin n) (S : Finset (Fin n)) : laplace i (χ S) = ite (i ∈ S) (χ S) 0 := by
  funext x
  rw [laplace_eq_dderiv, dderiv_walsh]
  split_ifs with h
  · unfold walshCharacter
    rw [← erase_eq, mul_prod_erase (s := S) (a := i) (f := fun i ↦ (-1 : ℝ) ^ (x i).val) h]
  · simp only [Pi.zero_apply, mul_zero]
end BooleanFun
