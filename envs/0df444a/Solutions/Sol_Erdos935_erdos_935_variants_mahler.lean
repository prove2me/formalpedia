-- Prove2me | solution 1 for Erdos935.erdos_935.variants.mahler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:54:16.712918+00:00
-- url     : https://prove2.me/submissions/39804eed-a1f6-4403-a0f3-e25840be4792

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
public import Theorems.Thm_Erdos935Proof_mahler

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935
namespace Erdos935
namespace erdos_935.variants
theorem _root_.solution :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      (1 - ε) * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) :=
  Erdos935Proof.mahler
end erdos_935.variants
end Erdos935
