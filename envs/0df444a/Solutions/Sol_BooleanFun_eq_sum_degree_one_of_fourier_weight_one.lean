-- Prove2me | solution 1 for BooleanFun.eq_sum_degree_one_of_fourier_weight_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:10:33.323694+00:00
-- url     : https://prove2.me/submissions/bddb805c-387d-4472-bb7a-cc7e04986ac4

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_eq_sum_fourier_of_fourier_weight
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
theorem _root_.solution {f : BooleanFunc n} (h : fourierWeight 1 f = ‖f‖ ^ 2) :
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by
  intro
  nth_rewrite 1 [eq_sum_fourier_of_fourier_weight h, Finset.sum_apply]
  apply sum_singletons
  intro
  simp only [Pi.smul_apply, prod_singleton, smul_eq_mul]
end BooleanFun
