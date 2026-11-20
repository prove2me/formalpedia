-- Prove2me | solution 1 for BooleanFun.dderiv_eq_sum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:14:26.556154+00:00
-- url     : https://prove2.me/submissions/d8f4897e-3147-4d7c-a7c9-68b397222d59

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_walsh_fourier
import Theorems.Thm_BooleanFun_dderiv_walsh

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (i : Fin n) (f : BooleanFunc n) : dderiv i f = ∑ S ∈ {S | i ∈ S}, 𝓕 f S•χ (S \ {i}) := by
  nth_rewrite 1 [walsh_fourier f]
  rw [map_sum, sum_filter]
  simp_rw [map_smul, dderiv_walsh]
  congr! 1; simp
end BooleanFun
