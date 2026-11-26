-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseProduct_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:45.545122+00:00
-- url     : https://prove2.me/submissions/27d36b19-95ab-44c3-b683-0bc0a245a0e1

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_one
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_nonneg
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_eq_prod_loss


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : 0 < n) (h : ℕ) :
    reverseProduct n h ≤ 1 := by
  rw [reverseProduct_eq_prod_loss]
  apply Finset.prod_le_one
  · intro i hi
    exact sub_nonneg.mpr (reverseLoss_le_one hn i)
  · intro i hi
    linarith [reverseLoss_nonneg n i]
end FirstPassageLinearTransport
