-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:03.63979+00:00
-- url     : https://prove2.me/submissions/f7b2eb74-7ae2-4b83-9f9a-fef1777c181f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution : shortcut 0 = 0 := by
  simp [shortcut]
end FirstPassageLinearTransport
