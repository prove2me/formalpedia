-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:48.773418+00:00
-- url     : https://prove2.me/submissions/adf78810-cb6a-482e-a8be-c0d720570b1d

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {n a b : ℕ} (hab : a ≤ b) :
    oddCount n a ≤ oddCount n b := by
  unfold oddCount
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro i _hi _hib
  omega
end FirstPassageLinearTransport
