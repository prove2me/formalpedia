-- Prove2me | solution 1 for FirstPassageLinearTransport.rank_transport_multiplier_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:16:28.403042+00:00
-- url     : https://prove2.me/submissions/a909c7da-8207-4278-a171-cf53e64d3b66

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℝ} (hr : 0 < r) (q : ℕ) :
    1 + 3 * (((q + 2 : ℕ) : ℝ) / r) ≤
      (1 + 6 / r) * ((q + 1 : ℕ) : ℝ) := by
  have hq2 : ((q + 2 : ℕ) : ℝ) ≤ 2 * ((q + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q]
  have hdiv :
      ((q + 2 : ℕ) : ℝ) / r ≤
        (2 * ((q + 1 : ℕ) : ℝ)) / r :=
    (div_le_div_iff_of_pos_right hr).2 hq2
  calc
    1 + 3 * (((q + 2 : ℕ) : ℝ) / r) ≤
        1 + 3 * ((2 * ((q + 1 : ℕ) : ℝ)) / r) := by
      linarith
    _ = 1 + 6 * (((q + 1 : ℕ) : ℝ) / r) := by ring
    _ ≤ ((q + 1 : ℕ) : ℝ) +
        6 * (((q + 1 : ℕ) : ℝ) / r) := by
      norm_num
    _ = (1 + 6 / r) * ((q + 1 : ℕ) : ℝ) := by ring
end FirstPassageLinearTransport
