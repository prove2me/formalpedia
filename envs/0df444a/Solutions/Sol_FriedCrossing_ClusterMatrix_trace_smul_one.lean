-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.trace_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:48:01.58353+00:00
-- url     : https://prove2.me/submissions/bfad2592-1f48-4a37-99a5-e287b79e4602

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution (s : ℝ) : (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)).trace = 2 * s := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]; push_cast; ring
end FriedCrossing.ClusterMatrix
