-- Prove2me | solution 1 for FriedCrossing.RateRatio.eventually_ne_zero_of_linearArrival
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:54:35.391208+00:00
-- url     : https://prove2.me/submissions/d7498ba9-daec-4a66-b2d7-392fe941eac4

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio
namespace FriedCrossing.RateRatio
theorem _root_.solution {f : ℝ → ℝ} {c σ : ℝ}
    (hf : LinearArrival f c σ) (hc : c ≠ 0) : ∀ᶠ τ in 𝓝[≠] σ, f τ ≠ 0 :=
  (hf.eventually_ne hc).mono fun τ hτ h0 => hτ (by rw [h0, zero_div])
end FriedCrossing.RateRatio
