-- Prove2me | solution 1 for FirstPassageLinearTransport.polylogTerminalRank_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:23.447383+00:00
-- url     : https://prove2.me/submissions/3ba86de7-e617-4036-8e7a-e819460e4997

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (A : ℝ) (M : ℕ) :
    A * Real.logb 2 ((M : ℝ) + 2) ≤
      (polylogTerminalRank A M : ℝ) := by
  exact Nat.le_ceil _
end FirstPassageLinearTransport
