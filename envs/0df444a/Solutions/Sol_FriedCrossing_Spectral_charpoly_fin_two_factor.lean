-- Prove2me | solution 1 for FriedCrossing.Spectral.charpoly_fin_two_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:33.6945+00:00
-- url     : https://prove2.me/submissions/acf5a5ac-c749-4916-9879-34900d54a571

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_eval_charpoly_fin_two

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {M : Matrix (Fin 2) (Fin 2) ℝ} {scl snc : ℝ}
    (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    M.charpoly = (X - C scl) * (X - C snc) := by
  apply Polynomial.funext
  intro z
  rw [eval_charpoly_fin_two, ← hs, ← hp]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  ring
end FriedCrossing.Spectral
