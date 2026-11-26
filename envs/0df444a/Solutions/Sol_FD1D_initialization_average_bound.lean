-- Prove2me | solution 1 for FD1D.initialization_average_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:05.81642+00:00
-- url     : https://prove2.me/submissions/6b85bb61-16f9-4b07-af09-cb6879b290ee

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {a m N mainCost : ℝ}
    (ha : 1 ≤ a) (hm : 0 < m) (hN : m ^ 2 ≤ N)
    (hmain : mainCost ≤ 6 * a / m) :
    m / N + mainCost ≤ 7 * a / m := by
  have hNpos : 0 < N := lt_of_lt_of_le (sq_pos_of_pos hm) hN
  have hinit : m / N ≤ 1 / m := by
    rw [div_le_div_iff₀ hNpos hm]
    nlinarith
  have hone : 1 / m ≤ a / m := by
    exact div_le_div_of_nonneg_right ha hm.le
  calc
    m / N + mainCost ≤ 1 / m + 6 * a / m :=
      add_le_add hinit hmain
    _ ≤ a / m + 6 * a / m := add_le_add_left hone _
    _ = 7 * a / m := by ring
end FD1D
