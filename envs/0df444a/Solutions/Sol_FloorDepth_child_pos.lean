-- Prove2me | solution 1 for FloorDepth.child_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/caa944b4-8e45-43e8-b7ea-6b6b9aadd51e

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m t e : ℕ) (hm : 0 < m) (ht : 0 < t) (he : m ≤ e) :
    0 < child m t e := Nat.mul_pos ht (Nat.div_pos he hm)
end FloorDepth
