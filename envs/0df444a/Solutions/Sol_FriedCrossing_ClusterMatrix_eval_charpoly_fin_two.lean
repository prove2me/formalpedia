-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.eval_charpoly_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:47:53.968188+00:00
-- url     : https://prove2.me/submissions/0af4252f-ccc6-42ee-afa8-3e94143ea580

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ) :
    M.charpoly.eval z = z ^ 2 - M.trace * z + M.det := by
  rw [eval_charpoly]
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.scalar_apply]
  ring
end FriedCrossing.ClusterMatrix
