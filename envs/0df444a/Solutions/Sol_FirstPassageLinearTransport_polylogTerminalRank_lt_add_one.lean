-- Prove2me | solution 1 for FirstPassageLinearTransport.polylogTerminalRank_lt_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:26.165185+00:00
-- url     : https://prove2.me/submissions/b1b7c2df-b808-410c-8aea-6d7b2b4fc79c

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℝ} (hA : 0 ≤ A) (M : ℕ) :
    (polylogTerminalRank A M : ℝ) <
      A * Real.logb 2 ((M : ℝ) + 2) + 1 := by
  apply Nat.ceil_lt_add_one
  have hx : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    nlinarith [show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M]
  exact mul_nonneg hA (Real.logb_nonneg (by norm_num) hx)
end FirstPassageLinearTransport
