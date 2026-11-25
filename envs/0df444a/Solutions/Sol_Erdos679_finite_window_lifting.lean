-- Prove2me | solution 1 for Erdos679.finite_window_lifting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:41:00.642355+00:00
-- url     : https://prove2.me/submissions/f5388a60-5e06-494d-8a49-63ec96d0e430

module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_CRT
public import Theorems.Thm_Erdos679_cardDistinctFactors_le_of_dvd

set_option autoImplicit false
@[expose] public section
public section
open Erdos679
namespace Erdos679
theorem _root_.solution (M K : ℕ) (hM : 0 < M) (F : ℕ → ℝ) (C : ℝ)
    (hwindow : ∀ k, K < k → k ≤ K + M →
      F k + C ≤ (ArithmeticFunction.cardDistinctFactors M : ℝ))
    {n : ℕ} (hn : K + M < n) :
    ∃ k < n, K < k ∧ F k + C ≤ (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  let k := K + 1 + (n - K - 1) % M
  have hr := Nat.mod_lt (n - K - 1) hM
  have hklo : K < k := by omega
  have hkhi : k ≤ K + M := by omega
  have hkn : k < n := by omega
  have hdiv : M ∣ n - k := by
    have heq := Nat.mod_add_div (n - K - 1) M
    refine ⟨(n - K - 1) / M, ?_⟩
    omega
  refine ⟨k, hkn, hklo, le_trans (hwindow k hklo hkhi) ?_⟩
  exact Nat.cast_le.mpr (cardDistinctFactors_le_of_dvd hdiv (by omega))
end Erdos679
