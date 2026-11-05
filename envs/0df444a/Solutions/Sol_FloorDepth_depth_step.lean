-- Prove2me | solution 1 for FloorDepth.depth_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/b1fbf3b4-dfe4-48a2-b9b7-c276b9d71754

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m t : ℕ) (ht : t < m) (e : ℕ) (he : m ≤ e) :
    depth m t ht e = 1 + depth m t ht (child m t e) := by
  rw [depth, dif_neg (Nat.not_lt_of_ge he)]
end FloorDepth
