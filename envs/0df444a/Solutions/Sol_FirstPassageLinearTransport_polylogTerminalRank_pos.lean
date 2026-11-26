-- Prove2me | solution 1 for FirstPassageLinearTransport.polylogTerminalRank_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:54.177109+00:00
-- url     : https://prove2.me/submissions/2a6d0c98-e7f3-4ace-922c-496a619b28ac

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
    {A : ℝ} (hA : 0 < A) (M : ℕ) :
    0 < polylogTerminalRank A M := by
  apply Nat.ceil_pos.mpr
  apply mul_pos hA
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  linarith
end FirstPassageLinearTransport
