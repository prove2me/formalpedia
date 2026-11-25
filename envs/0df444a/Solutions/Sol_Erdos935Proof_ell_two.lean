-- Prove2me | solution 1 for Erdos935Proof.ell_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:50:50.453885+00:00
-- url     : https://prove2.me/submissions/314d5de2-f41c-4291-a774-482d41b1bee0

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
public import Theorems.Thm_Erdos935Proof_parts_ii

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof
namespace Erdos935Proof
theorem _root_.solution : ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
    C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + 2), m) : ℕ) : ℝ) :=
  parts_ii 2 le_rfl
end Erdos935Proof
