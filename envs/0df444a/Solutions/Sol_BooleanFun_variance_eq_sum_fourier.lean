-- Prove2me | solution 1 for BooleanFun.variance_eq_sum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:09:52.19022+00:00
-- url     : https://prove2.me/submissions/130b75e8-dbcf-4988-a992-708be366df1d

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_covariance_eq_sum_fourier

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (f : BooleanFunc n) : variance f = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, (𝓕 f S) ^ 2 := by
  convert covariance_eq_sum_fourier f f; exact pow_two _
end BooleanFun
