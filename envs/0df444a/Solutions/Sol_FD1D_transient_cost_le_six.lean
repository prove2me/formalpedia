-- Prove2me | solution 1 for FD1D.transient_cost_le_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:13.096688+00:00
-- url     : https://prove2.me/submissions/728bc0d5-c1d3-441d-bd0f-15a3aee39a66

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
import Theorems.Thm_FD1D_transient_sqrt_term_le

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {a m T H cell cost : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hT : m ^ 2 ≤ T)
    (hcell : cell ≤ 2 * a / m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2) + 1 / T)
    (hcost :
      cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2)) :
    cost ≤ 6 * a / m := by
  have hsqrt := transient_sqrt_term_le hm hT hH0 hH
  have hterm :
      a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) ≤
        a * (4 / m) := by
    calc
      a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) =
          a * (Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6) := by ring
      _ ≤ a * (4 / m) := mul_le_mul_of_nonneg_left hsqrt ha
  calc
    cost ≤ cell +
        a / Real.sqrt 6 * Real.sqrt (H - 1 / m ^ 2) := hcost
    _ ≤ 2 * a / m + a * (4 / m) := add_le_add hcell hterm
    _ = 6 * a / m := by ring
end FD1D
