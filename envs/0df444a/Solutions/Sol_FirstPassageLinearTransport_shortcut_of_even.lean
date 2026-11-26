-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:34.80175+00:00
-- url     : https://prove2.me/submissions/6bceb679-7f62-4613-b3a5-81183f38c071

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : n % 2 = 0) :
    shortcut n = n / 2 := by
  simp [shortcut, hn]
end FirstPassageLinearTransport
