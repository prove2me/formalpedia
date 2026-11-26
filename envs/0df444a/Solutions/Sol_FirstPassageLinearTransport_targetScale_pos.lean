-- Prove2me | solution 1 for FirstPassageLinearTransport.targetScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:00.696796+00:00
-- url     : https://prove2.me/submissions/32af6888-4be8-432a-8f78-49e825e0e13f

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (r : ℝ) (M : ℕ) : 0 < targetScale r M := by
  unfold targetScale
  positivity
end FirstPassageLinearTransport
