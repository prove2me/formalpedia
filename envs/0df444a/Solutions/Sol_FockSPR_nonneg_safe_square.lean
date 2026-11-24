-- Prove2me | solution 1 for FockSPR.nonneg_safe_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:34.084501+00:00
-- url     : https://prove2.me/submissions/75e14f8e-c77b-48d3-831c-a5f6617ca7c8

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
theorem _root_.solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≥ b - c) : a ^ 2 ≥ (1 / 2) * b ^ 2 - c ^ 2 := by
  by_cases h : b ≤ c
  · nlinarith only [hb, hc, h, sq_nonneg a, sq_nonneg c]
  · nlinarith only [ha, hab, h, sq_nonneg (b - 2 * c)]
end FockSPR
