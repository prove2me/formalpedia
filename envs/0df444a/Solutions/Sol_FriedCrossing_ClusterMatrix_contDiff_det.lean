-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.contDiff_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:59:58.989742+00:00
-- url     : https://prove2.me/submissions/84896cbd-0e6d-43e1-8f2b-29830dd079c5

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {A : E → Matrix n n ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => (A x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)
end FriedCrossing.ClusterMatrix
