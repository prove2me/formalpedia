-- Prove2me | solution 1 for BooleanFun.influence_eq_sum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:48.897159+00:00
-- url     : https://prove2.me/submissions/5f61a067-0aa3-40dd-984d-fca907185990

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_inner_eq_expectation
import Theorems.Thm_BooleanFun_walsh_inner_eq
import Theorems.Thm_BooleanFun_laplace_eq_sum_fourier
import Theorems.Thm_BooleanFun_ite_ite_same


set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (f : BooleanFunc n) (i : Fin n):
    influence f i = ∑ S ∈ {S | i ∈ S}, (𝓕 f S) ^ 2 := by
  unfold influence
  nth_rewrite 1 [laplace_eq_sum_fourier]
  -- todo: simplify
  rw [pow_two, sum_mul_sum, map_sum, sum_filter]
  conv =>
    enter [1, 2, S]
    conv =>
      arg 2
      rw [map_sum]
      enter [2, S']
      rw [mul_smul_comm, map_smul, smul_mul_assoc, map_smul]
      rw [← inner_eq_expectation, walsh_inner_eq]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_filter,
      mem_univ, true_and, ite_ite_same]
  rw [← sum_filter]
  congr! 1; ring
end BooleanFun
