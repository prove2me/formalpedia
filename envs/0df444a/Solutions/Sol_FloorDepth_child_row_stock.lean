-- Prove2me | solution 1 for FloorDepth.child_row_stock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/980a0225-573b-4129-9b3d-0797fb620074

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth
import Theorems.Thm_FloorDepth_child_depth_drop

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m tmax t e W R : ℕ) (htmax : tmax < m)
    (ht : t ≤ tmax) (he : m ≤ e) (hW : 0 < W)
    (stock : W ^ depth m tmax htmax e ∣ R) :
    W ^ depth m tmax htmax (child m t e) ∣ R / W := by
  have hd := child_depth_drop m tmax t e htmax ht he
  have hpow : W ^ (depth m tmax htmax (child m t e) + 1) ∣ R :=
    dvd_trans (pow_dvd_pow W hd) stock
  obtain ⟨k, hk⟩ := hpow
  rw [hk, pow_succ]
  have heq : W ^ depth m tmax htmax (child m t e) * W * k / W =
      W ^ depth m tmax htmax (child m t e) * k := by
    rw [mul_assoc, mul_comm W k, ← mul_assoc, Nat.mul_div_left _ hW]
  rw [heq]
  exact dvd_mul_right _ _
end FloorDepth
