-- Prove2me | solution 1 for Erdos699.erdos_699.variants.of_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:16:13.823849+00:00
-- url     : https://prove2.me/submissions/d533d58a-c468-4c88-8602-19f19d160f46

module
public import Definitions.Def_Erdos699_Basic
public import Definitions.Def_Erdos699_Solution
public import Theorems.Thm_Erdos699_of_sq_lt


set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
namespace erdos_699.variants
theorem _root_.solution :
    ∀ n i j : ℕ,
      1 ≤ i →
      i < j →
      j ≤ n / 2 →
      j ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) :=
  Erdos699.of_sq_lt
end erdos_699.variants
end Erdos699
