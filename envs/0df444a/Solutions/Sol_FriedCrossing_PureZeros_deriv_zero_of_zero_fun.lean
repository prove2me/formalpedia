-- Prove2me | solution 1 for FriedCrossing.PureZeros.deriv_zero_of_zero_fun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:57:50.530956+00:00
-- url     : https://prove2.me/submissions/93163945-ec24-44a3-953f-aadd5859a196

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {g gτ : ℝ → ℝ} (h0 : ∀ τ, g τ = 0)
    (hd : ∀ τ, HasDerivAt g (gτ τ) τ) (τ : ℝ) : gτ τ = 0 := by
  have h1 : HasDerivAt g 0 τ := by
    have : g = fun _ => (0 : ℝ) := funext h0
    rw [this]; exact hasDerivAt_const τ (0 : ℝ)
  exact (hd τ).unique h1
end FriedCrossing.PureZeros
