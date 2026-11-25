-- Prove2me | solution 1 for Erdos685.choose_le_pow_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:41:48.870753+00:00
-- url     : https://prove2.me/submissions/e9f89216-2751-4228-9b4a-2df2c34eccd8

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_Erdos685ElementaryLowerBound_Solution

set_option autoImplicit false
@[expose] public section
public section
open Real Finset
open scoped ArithmeticFunction.omega
open Erdos685
namespace Erdos685
theorem _root_.solution {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    n.choose k ≤ n ^ (ω (n.choose k)) := by
  have hc : (n.choose k).primeFactors.card = ω (n.choose k) := by
    simp only [Nat.primeFactors, List.card_toFinset, ArithmeticFunction.cardDistinctFactors_apply]
  calc
    n.choose k = ∏ p ∈ (n.choose k).primeFactors,
        p ^ (n.choose k).factorization p := Nat.prod_primeFactors_pow_factorization (Nat.choose_ne_zero hk)
    _ ≤ ∏ _p ∈ (n.choose k).primeFactors, n :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun _ _ => Nat.pow_factorization_choose_le hn
    _ = n ^ (ω (n.choose k)) := by simp [hc]
end Erdos685
