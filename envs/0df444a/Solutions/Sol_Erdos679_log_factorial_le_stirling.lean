-- Prove2me | solution 1 for Erdos679.log_factorial_le_stirling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:20:19.281139+00:00
-- url     : https://prove2.me/submissions/42ab5dc9-d933-47ce-be79-959227c721bc

module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_StirlingBound

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * log n - n + 1 + log n / 2 := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
  change log (Stirling.stirlingSeq ((n - 1).succ)) ≤
    log (Stirling.stirlingSeq 1) at h
  have hsucc : (n - 1).succ = n := by omega
  rw [hsucc, Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne',
    Real.log_div hnpos.ne' (Real.exp_ne_zero _), Real.log_exp] at h
  linarith
end Erdos679
