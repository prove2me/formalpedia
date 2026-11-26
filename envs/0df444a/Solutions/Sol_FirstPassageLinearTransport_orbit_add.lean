-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:39.641082+00:00
-- url     : https://prove2.me/submissions/a93e0c4b-4df4-488e-8a48-147ae6da5183

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
theorem _root_.solution (j k n : ℕ) : orbit (j + k) n = orbit j (orbit k n) := by
  simp [orbit, Function.iterate_add_apply]
end FirstPassageLinearTransport
