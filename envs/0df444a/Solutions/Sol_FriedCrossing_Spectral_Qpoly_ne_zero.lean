-- Prove2me | solution 1 for FriedCrossing.Spectral.Qpoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:50:38.537896+00:00
-- url     : https://prove2.me/submissions/5dc92cc6-d7a3-4df2-8a37-acc3c209a751

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution (e₁ e₂ : ℝ) : Qpoly e₁ e₂ ≠ 0 := by
  intro h
  have := congrArg (fun p : ℝ[X] => p.coeff 2) h
  simp [Qpoly] at this
end FriedCrossing.Spectral
