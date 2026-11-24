-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.shannon_uniform_binary_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:56.621469+00:00
-- url     : https://prove2.me/submissions/7d475d05-9df1-4dae-adae-a3fc2530d4b9

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_uniform

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution (n : ℕ) :
    shannon (fun _ : Fin n → Bool =>
      1 / (Fintype.card (Fin n → Bool) : ℝ)) = (n : ℝ) * Real.log 2 := by
  rw [shannon_uniform]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
end BalanceSpecification.FiniteEntropy
