-- Prove2me | solution 1 for FloorDepth.depth_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/f0d0308c-e70f-4885-8d70-67ea829d3b4d

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth
import Theorems.Thm_FloorDepth_child_mono
import Theorems.Thm_FloorDepth_depth_base
import Theorems.Thm_FloorDepth_depth_step

set_option autoImplicit true
open FloorDepth
namespace FloorDepth
theorem _root_.solution (m t : ℕ) (ht : t < m) : Monotone (depth m t ht) := by
  intro e f hef
  induction f using Nat.strong_induction_on generalizing e with
  | h f ih =>
    by_cases hf : f < m
    · rw [depth_base m t ht f hf, depth_base m t ht e (lt_of_le_of_lt hef hf)]
    · have hfm : m ≤ f := Nat.le_of_not_gt hf
      by_cases he : e < m
      · rw [depth_base m t ht e he]; exact Nat.zero_le _
      · rw [depth_step m t ht f hfm, depth_step m t ht e (Nat.le_of_not_gt he)]
        exact Nat.add_le_add_left (ih (child m t f) (child_lt m t f ht hfm)
          (child_mono m t hef)) 1
end FloorDepth
