-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:53.084851+00:00
-- url     : https://prove2.me/submissions/582ce667-591b-433c-859c-1d4bb50c4368

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
theorem _root_.solution {n : ℕ} (hn : n % 2 = 1) :
    shortcut n = (3 * n + 1) / 2 := by
  simp [shortcut, hn]
end FirstPassageLinearTransport
