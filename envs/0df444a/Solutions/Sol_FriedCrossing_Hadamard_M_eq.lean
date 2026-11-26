-- Prove2me | solution 1 for FriedCrossing.Hadamard.M_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:45:56.175911+00:00
-- url     : https://prove2.me/submissions/13a7b8db-f3c7-4345-a337-2f1005860baf

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) :
    M θ τ = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ • Ndiv M M' sStar θ τ := by
  unfold Ndiv
  split_ifs with hτ
  · subst hτ; rw [h0, zero_smul, add_zero]
  · rw [smul_smul, mul_one_div_cancel hτ, one_smul, add_sub_cancel]
end FriedCrossing.Hadamard
