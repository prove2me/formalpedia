-- Prove2me | solution 1 for FriedCrossing.TwinRate.charpoly_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:55:02.458305+00:00
-- url     : https://prove2.me/submissions/884e3c22-21ea-4cfc-a585-dbdf08dc5bc5

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_add_wMinus
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_mul_wMinus

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {sStar τ a b : ℝ} (h : 0 ≤ disc a b) (z : ℝ) :
    z ^ 2 - clusterTrace sStar τ a * z + clusterDet sStar τ a b =
      (z - (sStar + τ * wPlus a b)) * (z - (sStar + τ * wMinus a b)) := by
  have h1 := wPlus_add_wMinus a b
  have h2 := wPlus_mul_wMinus h
  unfold clusterTrace clusterDet
  have : (z - (sStar + τ * wPlus a b)) * (z - (sStar + τ * wMinus a b)) =
      z ^ 2 - (2 * sStar + τ * (wPlus a b + wMinus a b)) * z +
        (sStar ^ 2 + sStar * τ * (wPlus a b + wMinus a b) + τ ^ 2 * (wPlus a b * wMinus a b)) := by
    ring
  rw [this, h1, h2]
end FriedCrossing.TwinRate
