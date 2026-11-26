-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:10.495136+00:00
-- url     : https://prove2.me/submissions/89c2e221-6e20-4c98-9198-3c7f3db77e0d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution (k n : ℕ) : orbit (k + 1) n = shortcut (orbit k n) := by
  simp [orbit, Function.iterate_succ_apply']
end FirstPassageLinearTransport
