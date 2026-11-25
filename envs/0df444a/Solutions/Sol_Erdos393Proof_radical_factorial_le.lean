-- Prove2me | solution 1 for Erdos393Proof.radical_factorial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:33:18.523986+00:00
-- url     : https://prove2.me/submissions/510cddb4-f73c-431b-84b0-df864018b4fb

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
public import Theorems.Thm_Erdos393Proof_radical_eq

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (n : ℕ) : radical n ! ≤ 4 ^ n := by
  refine le_trans (Nat.le_of_dvd (primorial_pos n) ?_) (primorial_le_four_pow n)
  rw [radical_eq, primorial]
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le
    ((Nat.Prime.dvd_factorial hp').1 (Nat.dvd_of_mem_primeFactors hp))), hp'⟩
end Erdos393Proof
