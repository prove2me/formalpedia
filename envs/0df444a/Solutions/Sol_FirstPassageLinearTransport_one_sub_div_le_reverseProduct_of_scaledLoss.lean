-- Prove2me | solution 1 for FirstPassageLinearTransport.one_sub_div_le_reverseProduct_of_scaledLoss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:31.522855+00:00
-- url     : https://prove2.me/submissions/1abdc248-71a1-4ab3-a121-61500fd4f388

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_one_sub_reverseLossTotal_le_reverseProduct
import Theorems.Thm_FirstPassageLinearTransport_reverseLossTotal_le_div_of_scaled_le

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Y n h : ℕ} {D : ℚ} (hn : 0 < n) (hY : 0 < Y)
    (hloss : scaledReverseLoss Y n h ≤ D) :
    1 - D / (Y : ℚ) ≤ reverseProduct n h := by
  have htotal := reverseLossTotal_le_div_of_scaled_le hY hloss
  exact (sub_le_sub_left htotal 1).trans
    (one_sub_reverseLossTotal_le_reverseProduct hn h)
end FirstPassageLinearTransport
