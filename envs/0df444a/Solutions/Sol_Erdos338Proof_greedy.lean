-- Prove2me | solution 1 for Erdos338Proof.greedy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:20.853107+00:00
-- url     : https://prove2.me/submissions/4fb751aa-50ff-4044-ac8d-92467e6848b4

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
public import Theorems.Thm_Erdos338Proof_mem_rep
public import Theorems.Thm_Erdos338Proof_exists_rep_avoid

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution (A : Set ℕ) (U : Finset ℕ) (Ms : Multiset ℕ)
    (hMs : ∀ m ∈ Ms, 2 * (#U + 2 * Multiset.card Ms) < #(rep A m)) :
    ∃ S : Finset ℕ, Disjoint U S ∧ (∀ x ∈ S, x ∈ A) ∧ #S = 2 * Multiset.card Ms ∧
      ∑ x ∈ S, x = Ms.sum := by
  classical
  induction Ms using Multiset.induction_on with
  | empty => exact ⟨∅, disjoint_empty_right _, by simp, by simp, by simp⟩
  | cons m Ms ih =>
    rw [Multiset.card_cons] at hMs
    obtain ⟨S, hUS, hSA, hScard, hSsum⟩ := ih fun x hx ↦ by
      have := hMs x (Multiset.mem_cons_of_mem hx)
      omega
    have hV : 2 * #(U ∪ S) < #(rep A m) := by
      have h1 := card_union_le U S
      have h2 := hMs m (Multiset.mem_cons_self m Ms)
      omega
    obtain ⟨a, ha, haV, hbV⟩ := exists_rep_avoid (U ∪ S) hV
    obtain ⟨ham, haA, hbA, hne⟩ := mem_rep.1 ha
    rw [mem_union, not_or] at haV hbV
    have hab : a ≠ m - a := by omega
    have haS : a ∉ insert (m - a) S := by
      rw [mem_insert, not_or]
      exact ⟨hab, haV.2⟩
    refine ⟨insert a (insert (m - a) S), ?_, ?_, ?_, ?_⟩
    · rw [disjoint_insert_right, disjoint_insert_right]
      exact ⟨haV.1, hbV.1, hUS⟩
    · intro x hx
      rw [mem_insert, mem_insert] at hx
      rcases hx with rfl | rfl | hx
      exacts [haA, hbA, hSA x hx]
    · rw [card_insert_of_notMem haS, card_insert_of_notMem hbV.2, hScard, Multiset.card_cons]
      ring
    · rw [sum_insert haS, sum_insert hbV.2, hSsum, Multiset.sum_cons]
      omega
end Erdos338Proof
