-- Prove2me | solution 1 for FD1D.stationary_sqrt_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:15.654392+00:00
-- url     : https://prove2.me/submissions/9b33a94d-3dff-4527-bfe4-787b4d9bd721

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
import Theorems.Thm_FD1D_sqrt_div_sqrt_six_le_four_div

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {H m : ℝ} (hm : 0 < m)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2)) :
    Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6 ≤ 4 / m := by
  apply sqrt_div_sqrt_six_le_four_div hm (sub_nonneg.2 hH0)
  calc
    H - 1 / m ^ 2 ≤ 206 / (3 * m ^ 2) - 1 / m ^ 2 :=
      sub_le_sub_right hH _
    _ ≤ 96 / m ^ 2 := by
      field_simp
      nlinarith
end FD1D
