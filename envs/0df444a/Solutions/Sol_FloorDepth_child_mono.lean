-- Prove2me | solution 1 for FloorDepth.child_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/5c13cffe-ce31-4963-a469-9340d9f994e8

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m t : ℕ) : Monotone (child m t) := by
  intro e f hef
  exact Nat.mul_le_mul_left t (Nat.div_le_div_right hef)
end FloorDepth
