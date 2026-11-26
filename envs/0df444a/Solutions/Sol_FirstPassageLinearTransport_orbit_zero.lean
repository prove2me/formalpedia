-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:34.242088+00:00
-- url     : https://prove2.me/submissions/1b9fb400-d234-4f05-9a9e-2d7805e5d2e7

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
theorem _root_.solution (n : ℕ) : orbit 0 n = n := by
  simp [orbit]
end FirstPassageLinearTransport
