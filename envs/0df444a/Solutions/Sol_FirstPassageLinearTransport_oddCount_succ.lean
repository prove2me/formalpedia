-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:03.902812+00:00
-- url     : https://prove2.me/submissions/d7b2e4a4-f39b-4201-a91a-c1358c1e5e49

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.oddCount_zero

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution (n k : ℕ) :
    oddCount n (k + 1) = oddCount n k + (parityBit n k : ℕ) := by
  simp [oddCount, Finset.sum_range_succ]
end FirstPassageLinearTransport
