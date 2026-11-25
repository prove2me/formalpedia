-- Prove2me | solution 1 for Erdos684.factorization_choose_pred_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:57:01.133294+00:00
-- url     : https://prove2.me/submissions/07026b71-242f-4619-8f8d-7d630a70bbbc

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
public import Theorems.Thm_Erdos684_pred_mod_prime_pow_ge
public import Theorems.Thm_Erdos684_no_carry_of_mod_le

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {M K p e : ℕ} (hM : 0 < M) (hp : p.Prime)
    (hlarge : K < p ^ e) (hdiv : p ^ e ∣ M) {k : ℕ} (hk : k ≤ K) :
    ((M - 1).choose k).factorization p = 0 := by
  by_cases hkn : k ≤ M - 1
  · rw [Nat.factorization_choose hp hkn (b := Nat.log p (M - 1) + 1) (by omega)]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    exact not_le.mpr (no_carry_of_mod_le hkn (pow_pos hp.pos _)
      (pred_mod_prime_pow_ge hM hp hlarge hdiv hk i))
  · rw [Nat.choose_eq_zero_of_lt (by omega : M - 1 < k)]
    simp
end Erdos684
