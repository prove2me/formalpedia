-- Prove2me | solution 1 for FirstPassageLinearTransport.rawCollatz_eq_shortcut_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:04.427461+00:00
-- url     : https://prove2.me/submissions/77700ee7-b743-43bb-9f7b-f3624a69ce31

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Theorems.Thm_FirstPassageLinearTransport_rawCollatz_of_even
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_even


set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : n % 2 = 0) :
    rawCollatz n = shortcut n := by
  rw [rawCollatz_of_even hn, shortcut_of_even hn]
end FirstPassageLinearTransport
