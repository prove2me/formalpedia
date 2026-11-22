-- Prove2me | solution 1 for Front.mem_tree_powK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:07.275722+00:00
-- url     : https://prove2.me/submissions/01b6fd0b-ecd7-4d78-b86a-26b7f0bca1ed

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_exists_extend_len

set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution (hM : StrictMono M) {k : ℕ} {s : List ℕ} :
    s ∈ tree (powK M k) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧ s.length ≤ k := by
  constructor
  · rintro ⟨t, ⟨htlen, htp, htM⟩, hpre⟩
    exact ⟨List.Pairwise.sublist hpre.sublist htp, fun x hx => htM x (hpre.subset hx),
      le_trans hpre.length_le (le_of_eq htlen)⟩
  · rintro ⟨hs, hsM, hlen⟩
    obtain ⟨t, hpre, ht, htM, htlen⟩ := exists_extend_len hM k s hs hsM hlen
    exact ⟨t, ⟨htlen, ht, htM⟩, hpre⟩
end Front
