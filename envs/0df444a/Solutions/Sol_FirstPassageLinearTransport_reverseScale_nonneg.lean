-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseScale_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:52.391725+00:00
-- url     : https://prove2.me/submissions/024d754e-df9b-4c77-b004-8a57aa15ede6

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution (n h : ℕ) : 0 ≤ reverseScale n h := by
  unfold reverseScale
  positivity
end FirstPassageLinearTransport
