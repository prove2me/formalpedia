-- Prove2me | solution 1 for FriedCrossing.ClusterMatrix.contDiff_charpoly_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:07.344804+00:00
-- url     : https://prove2.me/submissions/5fa3cb18-4e55-4391-b23d-82a97d26a913

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_det

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) (m : ℕ) (hm : m ≤ 4) :
    ContDiff ℝ k fun x => (A x).charpoly.coeff (4 - m) := by
  have heq : (fun x => (A x).charpoly.coeff (4 - m)) = fun x =>
      (-1 : ℝ) ^ m * ∑ s ∈ (Finset.univ : Finset (Fin 4)).powersetCard m,
        ((A x).submatrix (Subtype.val : s → Fin 4) (Subtype.val : s → Fin 4)).det := by
    funext x
    have := charpoly_coeff_eq_sum_minors (A x) m (by simpa using hm)
    simpa [Fintype.card_fin] using this
  rw [heq]
  exact contDiff_const.mul (ContDiff.sum fun s _ => contDiff_det fun i j => h _ _)
end FriedCrossing.ClusterMatrix
