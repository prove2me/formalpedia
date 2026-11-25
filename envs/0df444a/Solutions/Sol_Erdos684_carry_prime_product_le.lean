-- Prove2me | solution 1 for Erdos684.carry_prime_product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:57:02.313081+00:00
-- url     : https://prove2.me/submissions/8026e18d-3631-44d7-ad43-2e9539751aad

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
public import Theorems.Thm_Erdos684_factorization_choose_pos_of_mod_lt

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution (n k : ℕ) (hkn : k ≤ n) :
    (∏ p ∈ (Nat.primesLE k).filter (fun p => n % p < k % p), p) ≤
      smallPrimePart n k := by
  let s := (Nat.primesLE k).filter (fun p => n % p < k % p)
  calc
    (∏ p ∈ s, p) ≤ ∏ p ∈ s, p ^ ((n.choose k).factorization p) := by
      apply Finset.prod_le_prod'
      intro p hp
      obtain ⟨hpk, hmod⟩ := Finset.mem_filter.mp hp
      exact Nat.le_self_pow (Nat.ne_of_gt
        (factorization_choose_pos_of_mod_lt (Nat.prime_of_mem_primesLE hpk) hkn hmod)) p
    _ ≤ smallPrimePart n k := by
      apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
      intro p hp _
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero)
end Erdos684
