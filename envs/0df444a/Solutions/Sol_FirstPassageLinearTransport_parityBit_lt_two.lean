-- Prove2me | solution 1 for FirstPassageLinearTransport.parityBit_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:45.515084+00:00
-- url     : https://prove2.me/submissions/11515209-57ec-4d34-96b1-0db1487884aa

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution (n i : ℕ) : (parityBit n i : ℕ) < 2 :=
  (parityBit n i).isLt
end FirstPassageLinearTransport
