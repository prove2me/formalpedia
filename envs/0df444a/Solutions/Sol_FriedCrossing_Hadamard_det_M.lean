-- Prove2me | solution 1 for FriedCrossing.Hadamard.det_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:46:14.449346+00:00
-- url     : https://prove2.me/submissions/dc2c2259-4f4b-4341-b0c3-e673b5f639fa

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution (sStar τ : ℝ) (N : Matrix (Fin 2) (Fin 2) ℝ) :
    (sStar • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ • N).det =
      TwinRate.clusterDet sStar τ N.trace N.det := by
  simp [TwinRate.clusterDet, Matrix.det_fin_two, Matrix.trace_fin_two]; ring
end FriedCrossing.Hadamard
