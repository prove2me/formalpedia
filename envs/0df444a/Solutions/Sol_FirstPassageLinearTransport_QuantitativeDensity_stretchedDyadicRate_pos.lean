-- Prove2me | solution 1 for FirstPassageLinearTransport.QuantitativeDensity.stretchedDyadicRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:35:57.285422+00:00
-- url     : https://prove2.me/submissions/fbb8e3d2-4bc3-48c3-bc8b-e5f9ed1b1250

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount

set_option autoImplicit true
set_option maxHeartbeats 1000000
open FirstPassageLinearTransport
open FirstPassageLinearTransport.QuantitativeDensity
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport.QuantitativeDensity
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    0 < stretchedDyadicRate c := by
  unfold stretchedDyadicRate
  exact lt_min (div_pos hc (by norm_num))
    (div_pos (Real.log_pos (by norm_num)) (by norm_num))
end FirstPassageLinearTransport.QuantitativeDensity
