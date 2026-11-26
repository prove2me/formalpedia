-- Prove2me | solution 1 for FriedCrossing.Branch.zBranch_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:29.481799+00:00
-- url     : https://prove2.me/submissions/b29b690a-069a-4ae3-a161-e3762519dc3f

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Branch_wMinus_root
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_root


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Branch
open TwinRate PureZeros
namespace FriedCrossing.Branch
theorem _root_.solution (e₁ e₂ : ℝ → ℝ) (τ : ℝ) (hD : 0 ≤ disc (e₁ τ) (e₂ τ)) :
    zBranch e₁ e₂ τ ^ 2 - e₁ τ * zBranch e₁ e₂ τ + e₂ τ = 0 := by
  unfold zBranch
  split_ifs
  · exact wPlus_root hD
  · exact wMinus_root hD
end FriedCrossing.Branch
