-- Prove2me | solution 1 for FriedCrossing.TwinRate.cluster_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:56:19.234848+00:00
-- url     : https://prove2.me/submissions/bbcd46b0-d734-4ce8-aec7-e3b95e39abec

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_charpoly_factor

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {sStar τ a b : ℝ} (h : 0 ≤ disc a b) (z : ℝ) :
    z ^ 2 - clusterTrace sStar τ a * z + clusterDet sStar τ a b = 0 ↔
      z = sStar + τ * wPlus a b ∨ z = sStar + τ * wMinus a b := by
  rw [charpoly_factor h, mul_eq_zero, sub_eq_zero, sub_eq_zero]
end FriedCrossing.TwinRate
