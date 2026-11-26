-- Prove2me | solution 1 for FriedCrossing.TwinRate.hasDerivAt_disc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:45:09.875394+00:00
-- url     : https://prove2.me/submissions/54a64416-fdeb-44e5-b185-4223a1bfb6c4

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) :
    HasDerivAt (fun t => disc (A t) (B t)) (2 * A τ * a' - 4 * b') τ := by
  have h1 : HasDerivAt (fun t => A t * A t) (a' * A τ + A τ * a') τ := hA.mul hA
  have h2 : HasDerivAt (fun t => 4 * B t) (4 * b') τ := hB.const_mul 4
  have h3 := h1.sub h2
  have hfun : (fun t => disc (A t) (B t)) = fun t => A t * A t - 4 * B t := by
    funext t; simp [disc, sq]
  rw [hfun]
  exact h3.congr_deriv (by ring)
end FriedCrossing.TwinRate
