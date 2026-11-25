-- Prove2me | solution 1 for Erdos935Proof.le_B_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:39:13.079634+00:00
-- url     : https://prove2.me/submissions/31a32870-644b-481a-87a3-d2c6b8d10b70

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof
namespace Erdos935Proof
theorem _root_.solution {d N : ℕ} (hN : N ≠ 0) (hdN : d ∣ N) (hd : ∀ p, d.factorization p ≠ 1) :
    d ≤ Erdos367.B 2 N := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hN hdN
  have hle := (Nat.factorization_le_iff_dvd hd0 hN).2 hdN
  calc d = ∏ p ∈ d.factorization.support, p ^ d.factorization p :=
        (Nat.prod_factorization_pow_eq_self hd0).symm
    _ ≤ ∏ p ∈ d.factorization.support, p ^ N.factorization p :=
        Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun p hp ↦
          Nat.pow_le_pow_right (Nat.pos_of_mem_primeFactors (by simpa using hp)) (hle p)
    _ ≤ Erdos367.B 2 N := by
        unfold Erdos367.B
        refine Finset.prod_le_prod_of_subset_of_one_le (fun p hp ↦ ?_) (fun _ _ ↦ Nat.zero_le _) fun p hp _ ↦ ?_
        · have h1 := hd p
          have h2 := hle p
          rw [Finsupp.mem_support_iff] at hp
          rw [Finset.mem_filter, Finsupp.mem_support_iff]
          omega
        · exact Nat.one_le_pow _ _
            (Nat.pos_of_mem_primeFactors (by simpa using (Finset.mem_filter.1 hp).1))
end Erdos935Proof
