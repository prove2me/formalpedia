-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.det_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:59:30.430912+00:00
-- url     : https://prove2.me/submissions/95e1847b-fac9-4419-a116-7973a60e9580

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution (s : ℝ) : (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = s ^ 2 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
end FriedCrossing.ClusterMatrix
