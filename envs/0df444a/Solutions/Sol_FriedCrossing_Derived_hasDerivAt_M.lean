-- Prove2me | solution 1 for FriedCrossing.Derived.hasDerivAt_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:53:45.19563+00:00
-- url     : https://prove2.me/submissions/428cee04-93bf-476e-8826-6fb93c507519

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea
import Theorems.Thm_FriedCrossing_Regularity_differentiable_of_contDiff
import Theorems.Thm_FriedCrossing_Derived_two_add_one_le_three

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => M θ t i j) (Mτ M θ τ i j) τ :=
  hasDerivAt_pτ (f := fun θ τ => M θ τ i j)
    (differentiable_of_contDiff (f := fun θ τ => M θ τ i j) two_add_one_le_three (h.deg1 i j)) θ τ
end FriedCrossing.Derived
