-- Prove2me | solution 1 for BooleanFun.fourier_weight_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:14:31.978746+00:00
-- url     : https://prove2.me/submissions/fd68cc42-264d-47b7-a699-e29d90dad27c

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_sum_singletons


set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution {f : BooleanFunc n} : fourierWeight 1 f = fourierWeightOne f := by
  apply sum_singletons; intro; rfl
end BooleanFun
