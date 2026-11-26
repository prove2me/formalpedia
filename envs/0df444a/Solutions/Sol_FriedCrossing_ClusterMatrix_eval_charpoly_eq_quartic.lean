-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.eval_charpoly_eq_quartic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:00:44.721712+00:00
-- url     : https://prove2.me/submissions/4e300bf7-0f77-480a-9fdb-975ae882aea0

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_charpoly_natDegree

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution (A : Matrix (Fin 4) (Fin 4) ℝ) (z : ℝ) :
    A.charpoly.eval z = PureZeros.quartic (c₁ A) (c₂ A) (c₃ A) (c₄ A) z := by
  have hlead : A.charpoly.coeff 4 = 1 := by
    have := (charpoly_monic A).coeff_natDegree
    rwa [charpoly_natDegree] at this
  rw [eval_eq_sum_range, charpoly_natDegree]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, PureZeros.quartic, c₁, c₂, c₃, c₄,
    hlead]
  ring
end FriedCrossing.ClusterMatrix
