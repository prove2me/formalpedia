-- Prove2me | solution 1 for FriedCrossing.TwinRate.continuousAt_dwPlus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:55:46.321517+00:00
-- url     : https://prove2.me/submissions/ac8ba340-3e88-4165-9b6b-d06cb78e67d9

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {p : ℝ × ℝ × ℝ × ℝ} (hD : 0 < disc p.1 p.2.1) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => dwPlus q.1 q.2.1 q.2.2.1 q.2.2.2) p := by
  unfold dwPlus
  have hne : 2 * Real.sqrt (disc p.1 p.2.1) ≠ 0 :=
    mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr hD).ne'
  unfold disc at hne ⊢
  fun_prop (disch := exact hne)
end FriedCrossing.TwinRate
