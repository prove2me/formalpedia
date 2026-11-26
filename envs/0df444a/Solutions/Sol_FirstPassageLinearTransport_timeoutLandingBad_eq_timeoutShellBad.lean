-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutLandingBad_eq_timeoutShellBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:25:36.46334+00:00
-- url     : https://prove2.me/submissions/bf4257ee-cc24-46c5-82b1-af61d3b3d3bf

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (K₀ : ℝ) (L p : ℕ) :
    timeoutLandingBad K₀ L p = timeoutShellBad K₀ L (p - 1) := by
  rfl
end FirstPassageLinearTransport
