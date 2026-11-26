-- Prove2me | solution 1 for FirstPassageLinearTransport.QuantitativeDensity.stretchedShellScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:14.873911+00:00
-- url     : https://prove2.me/submissions/e89b08ee-20ac-4c7c-a214-4243f9497177

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
theorem _root_.solution (M : ℕ) :
    0 < stretchedShellScale M := by
  unfold stretchedShellScale
  positivity
end FirstPassageLinearTransport.QuantitativeDensity
