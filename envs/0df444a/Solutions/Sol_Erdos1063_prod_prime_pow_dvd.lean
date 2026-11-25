-- Prove2me | solution 1 for Erdos1063.prod_prime_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:31:22.116094+00:00
-- url     : https://prove2.me/submissions/d7674a22-630f-446c-8456-bf89701220a4

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (f : ℕ → ℕ) {m : ℕ}
    (h : ∀ p ∈ s, p ^ f p ∣ m) : ∏ p ∈ s, p ^ f p ∣ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq]
    have hqs := hs q (Finset.mem_insert_self q s)
    have ih' := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
      (fun p hp => h p (Finset.mem_insert_of_mem hp))
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h q (Finset.mem_insert_self q s)) ih'
    apply Nat.Coprime.prod_right
    intro p hp
    have hpp := hs p (Finset.mem_insert_of_mem hp)
    have hne : q ≠ p := fun h' => hq (h' ▸ hp)
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hqs hpp).mpr hne)
end Erdos1063
