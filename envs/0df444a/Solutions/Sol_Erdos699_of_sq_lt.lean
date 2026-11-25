-- Prove2me | solution 1 for Erdos699.of_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:06:20.39954+00:00
-- url     : https://prove2.me/submissions/38ad9edc-24ee-47d3-a0b8-98c850aced70

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
public import Theorems.Thm_Erdos699_le_sq_of_counterexample

set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
theorem _root_.solution :
    ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 → j ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  intro n i j hi hij hjn hsq
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have := le_sq_of_counterexample hi hij hjn hcon
  omega
end Erdos699
