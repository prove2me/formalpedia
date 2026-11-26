-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.charpoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:58:59.23816+00:00
-- url     : https://prove2.me/submissions/001d5640-ea21-49e1-956c-5665c4fc15c2

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution (A : Matrix (Fin 4) (Fin 4) ℝ) : A.charpoly.natDegree = 4 := by
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
end FriedCrossing.ClusterMatrix
