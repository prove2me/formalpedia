-- Prove2me | solution 1 for FriedCrossing.Hadamard.trace_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:46:11.708085+00:00
-- url     : https://prove2.me/submissions/0ae1c3c8-fb3d-4f6b-842a-b4e8645ab773

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution (sStar τ : ℝ) (N : Matrix (Fin 2) (Fin 2) ℝ) :
    (sStar • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ • N).trace =
      TwinRate.clusterTrace sStar τ N.trace := by
  simp [TwinRate.clusterTrace, Matrix.trace_fin_two]; ring
end FriedCrossing.Hadamard
