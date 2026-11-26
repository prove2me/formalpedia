-- Prove2me | solution 1 for FirstPassageLinearTransport.stirlingSeq_eq_factorial_div_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:22.264102+00:00
-- url     : https://prove2.me/submissions/f5633a44-54eb-445d-a914-6a3080a0e0f7

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) :
    Stirling.stirlingSeq n = (Nat.factorial n : ℝ) / stirlingCore n := by
  rfl
end FirstPassageLinearTransport
