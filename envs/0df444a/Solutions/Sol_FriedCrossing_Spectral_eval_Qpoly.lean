-- Prove2me | solution 1 for FriedCrossing.Spectral.eval_Qpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:33.258421+00:00
-- url     : https://prove2.me/submissions/d87a509e-3494-41a2-b863-c4c16fe2cefa

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution (e₁ e₂ z : ℝ) : (Qpoly e₁ e₂).eval z = z ^ 2 - e₁ * z + e₂ := by
  simp [Qpoly]
end FriedCrossing.Spectral
