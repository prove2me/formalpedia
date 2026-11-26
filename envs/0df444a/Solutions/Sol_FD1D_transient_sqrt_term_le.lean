-- Prove2me | solution 1 for FD1D.transient_sqrt_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:26.917705+00:00
-- url     : https://prove2.me/submissions/6314cf27-6787-4f4d-9b0c-b4e0f4e29ed2

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
import Theorems.Thm_FD1D_sqrt_div_sqrt_six_le_four_div
import Theorems.Thm_FD1D_inv_horizon_le_inv_sq

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {H T m : ℝ} (hm : 0 < m) (hT : m ^ 2 ≤ T)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2) + 1 / T) :
    Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6 ≤ 4 / m := by
  apply sqrt_div_sqrt_six_le_four_div hm (sub_nonneg.2 hH0)
  have hInv := inv_horizon_le_inv_sq hm hT
  calc
    H - 1 / m ^ 2
        ≤ 206 / (3 * m ^ 2) + 1 / T - 1 / m ^ 2 :=
      sub_le_sub_right hH _
    _ ≤ 206 / (3 * m ^ 2) := by linarith
    _ ≤ 96 / m ^ 2 := by
      have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
      apply (div_le_div_iff₀ (by positivity) hm2).2
      field_simp
      norm_num
end FD1D
