-- Prove2me | solution 1 for FloorDepth.row_split_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/c17707b7-81ae-40cf-8df9-b4f236382c52

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth
import Theorems.Thm_FloorDepth_depth_step

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m tmax e W R : ℕ) (htmax : tmax < m) (he : m ≤ e)
    (stock : W ^ depth m tmax htmax e ∣ R) : W * (R / W) = R := by
  have hd : 1 ≤ depth m tmax htmax e := by rw [depth_step m tmax htmax e he]; omega
  have hw : W ∣ R := dvd_trans (by simpa using pow_dvd_pow W hd) stock
  exact Nat.mul_div_cancel' hw
end FloorDepth
