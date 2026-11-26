-- Prove2me | solution 1 for FirstPassageLinearTransport.clockThreshold_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:26:20.049935+00:00
-- url     : https://prove2.me/submissions/556f8162-905c-4c4a-a4ee-b1f329e575ad

import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : clockThreshold < 1 := by
  unfold clockThreshold
  have : 0 < 1 / ((6953 / 1000 : ℝ) * Real.log 2) := by positivity
  linarith
end FirstPassageLinearTransport
