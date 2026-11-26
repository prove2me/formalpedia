-- Prove2me | solution 1 for FriedCrossing.Derived.clusterC1_of_C3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:23.311873+00:00
-- url     : https://prove2.me/submissions/20ca04fb-df24-44c6-9f5d-b084b6d72ecb

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429
import Theorems.Thm_FriedCrossing_Derived_hasDerivAt_M

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) : ClusterC1 M (Mτ M) where
  deriv := hasDerivAt_M h
  cont i j := (contDiff_Mτ h i j).continuous.continuousAt
end FriedCrossing.Derived
