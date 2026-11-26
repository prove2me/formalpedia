-- Prove2me | solution 1 for FriedCrossing.Spectral.coeffs_of_mirror
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:02:15.54065+00:00
-- url     : https://prove2.me/submissions/1177e408-8755-4df8-a15b-a1fca3fba5b9

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_eval_charpoly_eq_quartic

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {A : Matrix (Fin 4) (Fin 4) ℝ} {s : ℝ}
    (h : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : c₁ A = 2 * s ∧ c₂ A = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  simp only [eval_charpoly_eq_quartic, PureZeros.quartic] at h0 h1 hm h2
  ring_nf at h0 h1 hm h2
  constructor <;> linarith
end FriedCrossing.Spectral
