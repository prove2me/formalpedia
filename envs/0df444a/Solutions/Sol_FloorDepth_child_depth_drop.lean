-- Prove2me | solution 1 for FloorDepth.child_depth_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/0f3ac247-1208-4fda-b966-decaf01ed88e

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth
import Theorems.Thm_FloorDepth_depth_step
import Theorems.Thm_FloorDepth_depth_mono

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m tmax t e : ℕ) (htmax : tmax < m)
    (ht : t ≤ tmax) (he : m ≤ e) :
    depth m tmax htmax (child m t e) + 1 ≤ depth m tmax htmax e := by
  rw [depth_step m tmax htmax e he]
  have hc : child m t e ≤ child m tmax e := Nat.mul_le_mul_right (e / m) ht
  have hd := depth_mono m tmax htmax hc
  omega
end FloorDepth
