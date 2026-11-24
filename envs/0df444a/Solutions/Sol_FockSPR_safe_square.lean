-- Prove2me | solution 1 for FockSPR.safe_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:54.874882+00:00
-- url     : https://prove2.me/submissions/4be47a7a-c5a1-4fb7-86dc-a326379a8257

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_SafeSquare

set_option autoImplicit true
@[expose] public section
public section
open Real
open FockSPR
namespace FockSPR
theorem _root_.solution (a b : ℝ) : (a + b) ^ 2 ≥ (1 / 2) * a ^ 2 - b ^ 2 := by
  nlinarith only [sq_nonneg (a + 2 * b)]
end FockSPR
