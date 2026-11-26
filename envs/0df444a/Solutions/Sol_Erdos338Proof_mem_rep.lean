-- Prove2me | solution 1 for Erdos338Proof.mem_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:06.64806+00:00
-- url     : https://prove2.me/submissions/c5b80edc-7c73-4abf-ab63-21ab39745c28

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {A : Set ℕ} {m a : ℕ} :
    a ∈ rep A m ↔ a ≤ m ∧ a ∈ A ∧ m - a ∈ A ∧ 2 * a ≠ m := by
  simp [rep]
end Erdos338Proof
