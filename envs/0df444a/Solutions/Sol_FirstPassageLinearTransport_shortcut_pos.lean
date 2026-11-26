-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:31.173588+00:00
-- url     : https://prove2.me/submissions/0da3d3fc-6dde-4e07-9ce6-a4ce559a1a98

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_even
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_odd

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : 0 < n) : 0 < shortcut n := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · rw [shortcut_of_even heven]
    apply Nat.div_pos
    · omega
    · omega
  · rw [shortcut_of_odd hodd]
    apply Nat.div_pos
    · omega
    · omega
end FirstPassageLinearTransport
