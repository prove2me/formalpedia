-- Prove2me | solution 1 for BooleanFun.walsh_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:05:56.447195+00:00
-- url     : https://prove2.me/submissions/aebc334c-f2f2-4e46-bd11-c5264676facf

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_inner_eq_sum_fourier

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution : ‖f‖^2 = ∑ S : Finset (Fin n), |𝓕 f S|^2 := by
  simp_rw [norm_sq_eq_inner, inner_eq_sum_fourier (f := f) (g := f), sq_abs, pow_two]
end BooleanFun
