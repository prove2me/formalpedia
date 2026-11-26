-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_gt_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:11.354997+00:00
-- url     : https://prove2.me/submissions/83ba844d-3d42-44cb-9692-6a2dc177df0f

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {x : ℕ} (hodd : x % 2 = 1) : x < shortcut x := by
  have hstep := two_mul_shortcut_of_odd hodd
  omega
end FirstPassageLinearTransport
