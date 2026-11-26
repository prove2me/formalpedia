-- Prove2me | solution 1 for FriedCrossing.PureZeros.hasDerivAt_wMinus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:58:12.396844+00:00
-- url     : https://prove2.me/submissions/86e35a3d-498e-4cc3-9755-063befc7ee7b

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_disc


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) (hD : 0 < disc (A τ) (B τ)) :
    HasDerivAt (fun t => wMinus (A t) (B t)) (dwMinus (A τ) (B τ) a' b') τ := by
  unfold wMinus dwMinus
  have hs : HasDerivAt (fun t => Real.sqrt (disc (A t) (B t)))
      ((2 * A τ * a' - 4 * b') / (2 * Real.sqrt (disc (A τ) (B τ)))) τ :=
    (hasDerivAt_disc hA hB).sqrt hD.ne'
  exact (hA.sub hs).div_const 2
end FriedCrossing.PureZeros
