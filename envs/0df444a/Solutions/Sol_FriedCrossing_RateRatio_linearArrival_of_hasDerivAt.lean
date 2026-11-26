-- Prove2me | solution 1 for FriedCrossing.RateRatio.linearArrival_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:44:08.676797+00:00
-- url     : https://prove2.me/submissions/0b7897cf-4779-45f9-8df9-276a227b622c

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio
namespace FriedCrossing.RateRatio
theorem _root_.solution {f : ℝ → ℝ} {c σ : ℝ} (hf : HasDerivAt f c σ)
    (h0 : f σ = 0) : LinearArrival f c σ := by
  have h := hasDerivAt_iff_tendsto_slope.mp hf
  refine h.congr' (Eventually.of_forall fun τ => ?_)
  rw [slope_def_field, h0, sub_zero]
end FriedCrossing.RateRatio
