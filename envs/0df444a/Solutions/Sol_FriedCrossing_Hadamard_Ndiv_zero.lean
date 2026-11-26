-- Prove2me | solution 1 for FriedCrossing.Hadamard.Ndiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:45:53.212691+00:00
-- url     : https://prove2.me/submissions/806ad96e-7e8f-4cd8-8bf1-c6d25c94fb37

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ) (θ : ℝ) :
    Ndiv M M' sStar θ 0 = M' θ 0 := by simp [Ndiv]
end FriedCrossing.Hadamard
