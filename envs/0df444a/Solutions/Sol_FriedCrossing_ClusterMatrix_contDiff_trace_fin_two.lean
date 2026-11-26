-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.contDiff_trace_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:48:30.447886+00:00
-- url     : https://prove2.me/submissions/b248e13a-e300-485b-8b23-9aee8dabd280

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => M x i j) : ContDiff ℝ k fun x => (M x).trace := by
  simp only [Matrix.trace_fin_two]; exact (h 0 0).add (h 1 1)
end FriedCrossing.ClusterMatrix
