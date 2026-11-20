-- Prove2me | solution 1 for BooleanFun.eq_sum_degree_one_of_fourier_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:01.651393+00:00
-- url     : https://prove2.me/submissions/bd24484a-0aca-41b7-a7b7-98d7d3450416

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_fourier_eq_zero_iff_fourier_weight_eq
import Theorems.Thm_BooleanFun_eq_sum_degree_one_of_fourier_weight_one

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution {f : BooleanFunc n} (h : ∀ S, S.card ≠ 1 → 𝓕 f S = 0):
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val :=
  eq_sum_degree_one_of_fourier_weight_one (fourier_eq_zero_iff_fourier_weight_eq.mp h)
end BooleanFun
