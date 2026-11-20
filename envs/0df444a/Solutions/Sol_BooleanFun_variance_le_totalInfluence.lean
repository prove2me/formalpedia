-- Prove2me | solution 1 for BooleanFun.variance_le_totalInfluence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:14:29.210459+00:00
-- url     : https://prove2.me/submissions/b7a46b2e-b80e-44f1-b21c-7bf947ac9261

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_totalInfluence_eq_sum_fourier
import Theorems.Thm_BooleanFun_variance_eq_sum_fourier

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (f : BooleanFunc n) : variance f ≤ totalInfluence f := by
  rw [variance_eq_sum_fourier, totalInfluence_eq_sum_fourier, sum_filter]
  gcongr with S
  split_ifs with h
  · nth_rewrite 1 [← one_mul ((𝓕 f S)^2)]
    gcongr
    simp only [Nat.one_le_cast, one_le_card, h]
  · rw [← zero_mul 0]
    gcongr
    simp only [Nat.cast_nonneg]
    exact sq_nonneg (𝓕 f S)
end BooleanFun
