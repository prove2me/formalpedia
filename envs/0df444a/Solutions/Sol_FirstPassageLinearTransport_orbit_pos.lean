-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:07.839838+00:00
-- url     : https://prove2.me/submissions/f182ef02-45d9-43c2-a611-d72006cdf3fb

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < orbit k n := by
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [orbit_succ]
      exact shortcut_pos ih
end FirstPassageLinearTransport
