-- Prove2me | solution 1 for FriedCrossing.TwinRate.hasDerivAt_wPlus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:46:07.350562+00:00
-- url     : https://prove2.me/submissions/44ce2d10-2a45-437e-8491-e299491286e7

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_disc

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) (hD : 0 < disc (A τ) (B τ)) :
    HasDerivAt (fun t => wPlus (A t) (B t)) (dwPlus (A τ) (B τ) a' b') τ := by
  unfold wPlus dwPlus
  have hs : HasDerivAt (fun t => Real.sqrt (disc (A t) (B t)))
      ((2 * A τ * a' - 4 * b') / (2 * Real.sqrt (disc (A τ) (B τ)))) τ :=
    (hasDerivAt_disc hA hB).sqrt hD.ne'
  exact (hA.add hs).div_const 2
end FriedCrossing.TwinRate
