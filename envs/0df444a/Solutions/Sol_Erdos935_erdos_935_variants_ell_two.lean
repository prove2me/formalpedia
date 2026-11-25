-- Prove2me | solution 1 for Erdos935.erdos_935.variants.ell_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:55:13.496832+00:00
-- url     : https://prove2.me/submissions/fd1a42d8-2fe1-4ca4-8150-85267f0eaade

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
public import Theorems.Thm_Erdos935Proof_ell_two

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935
namespace Erdos935
namespace erdos_935.variants
theorem _root_.solution :
    ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + 2), m) : ℕ) : ℝ) :=
  Erdos935Proof.ell_two
end erdos_935.variants
end Erdos935
