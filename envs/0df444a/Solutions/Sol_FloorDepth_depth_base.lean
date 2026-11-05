-- Prove2me | solution 1 for FloorDepth.depth_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/6161c4f3-1f19-449e-889b-44bb2e5c195c

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m t : ℕ) (ht : t < m) (e : ℕ) (he : e < m) :
    depth m t ht e = 0 := by rw [depth, dif_pos he]
end FloorDepth
