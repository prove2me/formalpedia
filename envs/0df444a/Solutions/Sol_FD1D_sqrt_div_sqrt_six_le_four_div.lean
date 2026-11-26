-- Prove2me | solution 1 for FD1D.sqrt_div_sqrt_six_le_four_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:19.351801+00:00
-- url     : https://prove2.me/submissions/1ce7c2e5-fe4a-4ed6-9ec9-1088aead9dde

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {x m : ℝ} (hm : 0 < m) (hx0 : 0 ≤ x)
    (hx : x ≤ 96 / m ^ 2) :
    Real.sqrt x / Real.sqrt 6 ≤ 4 / m := by
  have hsix : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  rw [div_le_iff₀ hsix]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      x ≤ 96 / m ^ 2 := hx
      _ = (4 / m * Real.sqrt 6) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
        field_simp
        <;> ring
end FD1D
