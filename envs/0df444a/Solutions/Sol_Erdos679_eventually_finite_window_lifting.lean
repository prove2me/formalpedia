-- Prove2me | solution 1 for Erdos679.eventually_finite_window_lifting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:49:14.753426+00:00
-- url     : https://prove2.me/submissions/bc0b9ffb-dd9c-44cc-b3cd-e8641d31683a

module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_CRT
public import Theorems.Thm_Erdos679_finite_window_lifting

set_option autoImplicit false
@[expose] public section
public section
open Erdos679
namespace Erdos679
theorem _root_.solution (M K : ℕ) (hM : 0 < M) (F : ℕ → ℝ) (C : ℝ)
    (hwindow : ∀ k, K < k → k ≤ K + M →
      F k + C ≤ (ArithmeticFunction.cardDistinctFactors M : ℝ)) :
    ∀ᶠ n in Filter.atTop,
      ∃ k < n, K < k ∧ F k + C ≤ (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨K + M + 1, ?_⟩
  intro n hn
  exact finite_window_lifting M K hM F C hwindow (by omega)
end Erdos679
