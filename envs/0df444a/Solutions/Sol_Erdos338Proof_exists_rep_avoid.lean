-- Prove2me | solution 1 for Erdos338Proof.exists_rep_avoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:07.625543+00:00
-- url     : https://prove2.me/submissions/d5fcfa86-9faa-4a3c-9f97-195a8cbdc408

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
public import Theorems.Thm_Erdos338Proof_mem_rep

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {A : Set ℕ} {m : ℕ} (V : Finset ℕ) (h : 2 * #V < #(rep A m)) :
    ∃ a ∈ rep A m, a ∉ V ∧ m - a ∉ V := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : rep A m ⊆ V ∪ V.image (m - ·) := by
    intro a ha
    rw [mem_union, mem_image]
    by_cases haV : a ∈ V
    · exact Or.inl haV
    · refine Or.inr ⟨m - a, hcon a ha haV, ?_⟩
      have := (mem_rep.1 ha).1
      omega
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 : #(V.image (m - ·)) ≤ #V := card_image_le
  omega
end Erdos338Proof
