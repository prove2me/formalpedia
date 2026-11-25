-- Prove2me | solution 1 for Erdos935.erdos_935.parts.ii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:50:54.031807+00:00
-- url     : https://prove2.me/submissions/c23752b9-1fcf-4746-bf61-2daaeeb2a785

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
public import Theorems.Thm_Erdos935Proof_parts_ii

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935
namespace Erdos935
namespace erdos_935.parts
theorem _root_.solution :
    ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) :=
  Erdos935Proof.parts_ii
end erdos_935.parts
end Erdos935
