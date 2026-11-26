-- Prove2me | solution 1 for FriedCrossing.TwinRate.hasDerivAt_twin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:55:42.007615+00:00
-- url     : https://prove2.me/submissions/8ceeef52-dff4-4e76-a9c9-9fd160e7eea4

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_wPlus

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {sStar : ℝ → ℝ} {a b a' b' : ℝ → ℝ → ℝ} {θ τ : ℝ}
    (hA : HasDerivAt (a θ) (a' θ τ) τ) (hB : HasDerivAt (b θ) (b' θ τ) τ)
    (hD : 0 < disc (a θ τ) (b θ τ)) :
    HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ := by
  unfold twin dtwin
  have hw := hasDerivAt_wPlus hA hB hD
  have hτ : HasDerivAt (fun t : ℝ => t) 1 τ := hasDerivAt_id τ
  have hprod := hτ.mul hw
  have := (hasDerivAt_const τ (sStar θ)).add hprod
  exact this.congr_deriv (by ring)
end FriedCrossing.TwinRate
