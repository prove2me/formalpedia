-- Prove2me | solution 1 for BalanceSpecification.exists_bounded_bridge_of_synchronizing_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:32.396115+00:00
-- url     : https://prove2.me/submissions/d406a78a-c01f-4934-90e4-02e680133108

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Theorems.Thm_BalanceSpecification_IsFactorial_prefix
public import Theorems.Thm_BalanceSpecification_IsFactorial_suffix
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution
    (hL : IsFactorial L) {v : Word A} (hv : IsSynchronizing L v) {N : ℕ}
    {u w : Word A}
    (hF : ∃ s : Word A, s.length ≤ N ∧ u ++ s ∈ L ∧ v <:+: s)
    (hP : ∃ p : Word A, p.length ≤ N ∧ p ++ w ∈ L ∧ v <:+: p) :
    ∃ b ∈ L, b.length ≤ 2 * N ∧ u ++ b ++ w ∈ L := by
  obtain ⟨s, hsN, hus, ⟨a, c, rfl⟩⟩ := hF
  obtain ⟨p, hpN, hpw, ⟨d, e, rfl⟩⟩ := hP
  have huav : (u ++ a) ++ v ∈ L := by
    apply hL.prefix (v := c)
    simpa only [List.append_assoc] using hus
  have hvew : v ++ (e ++ w) ∈ L := by
    apply hL.suffix (u := d)
    simpa only [List.append_assoc] using hpw
  have hglue : u ++ (a ++ v ++ e) ++ w ∈ L := by
    simpa only [List.append_assoc] using hv.2 (u ++ a) (e ++ w) huav hvew
  refine ⟨a ++ v ++ e, ?_, ?_, hglue⟩
  · apply hL (u := a ++ v ++ e) (v := u ++ (a ++ v ++ e) ++ w) _ hglue
    exact ⟨u, w, rfl⟩
  · simp only [List.length_append] at hsN hpN ⊢
    omega
end BalanceSpecification
