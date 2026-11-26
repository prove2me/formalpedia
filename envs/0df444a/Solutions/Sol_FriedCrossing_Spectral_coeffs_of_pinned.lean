-- Prove2me | solution 1 for FriedCrossing.Spectral.coeffs_of_pinned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:02:31.605405+00:00
-- url     : https://prove2.me/submissions/8f3096d7-0aa2-4455-b22a-26edf144b3a4

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
theorem _root_.solution {A : Matrix (Fin 4) (Fin 4) ℝ} {t : ℝ}
    (h : ∀ z, A.charpoly.eval z = z ^ 3 * (z - t)) : c₁ A = t ∧ c₂ A = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  simp only [eval_charpoly_eq_quartic, PureZeros.quartic] at h0 h1 hm h2
  ring_nf at h0 h1 hm h2
  constructor <;> linarith
end FriedCrossing.Spectral
