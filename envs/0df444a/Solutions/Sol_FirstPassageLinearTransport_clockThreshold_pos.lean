-- Prove2me | solution 1 for FirstPassageLinearTransport.clockThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:46.759496+00:00
-- url     : https://prove2.me/submissions/ad7d9656-fe28-4b5e-8a94-a9392e039f2b

import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_clockThreshold
import Theorems.Thm_FirstPassageLinearTransport_a0_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 0 < clockThreshold :=
  a0_pos.trans a0_lt_clockThreshold
end FirstPassageLinearTransport
