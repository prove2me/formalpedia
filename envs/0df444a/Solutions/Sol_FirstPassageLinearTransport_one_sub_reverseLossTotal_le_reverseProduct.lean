-- Prove2me | solution 1 for FirstPassageLinearTransport.one_sub_reverseLossTotal_le_reverseProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:42.371269+00:00
-- url     : https://prove2.me/submissions/5d2cfba6-79ac-412d-86bf-6d1551b7bc7a

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_one_sub_sum_le_prod
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_one
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_nonneg
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_eq_prod_loss


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) (h : ℕ) :
    1 - reverseLossTotal n h ≤ reverseProduct n h := by
  rw [reverseLossTotal, reverseProduct_eq_prod_loss]
  apply one_sub_sum_le_prod
  intro i hi
  exact ⟨reverseLoss_nonneg n i, reverseLoss_le_one hn i⟩
end FirstPassageLinearTransport
