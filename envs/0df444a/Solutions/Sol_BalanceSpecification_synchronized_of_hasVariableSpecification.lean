-- Prove2me | solution 1 for BalanceSpecification.synchronized_of_hasVariableSpecification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:51.82384+00:00
-- url     : https://prove2.me/submissions/6fc24ed9-9b40-4bc3-8c1c-a0ba748bb0a0

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Theorems.Thm_BalanceSpecification_IsFactorial_prefix
public import Theorems.Thm_BalanceSpecification_IsFactorial_suffix
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_irreducible_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_language_factorial
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
    [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) (h : HasVariableSpecification X) : Synchronized X := by
  classical
  refine ⟨irreducible_of_hasVariableSpecification h, ?_⟩
  obtain ⟨N, hN⟩ := h
  let bridges : Word A → Word A → Finset (Word A) := fun u v =>
    ((Finset.range (N + 1)).biUnion (fun n => allWords (A := A) n)).filter
      (fun b => u ++ b ++ v ∈ language X)
  have mem_bridges {u v b : Word A} : b ∈ bridges u v ↔
      b.length ≤ N ∧ u ++ b ++ v ∈ language X := by
    simp only [bridges, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_range, mem_allWords]
    constructor
    · rintro ⟨⟨n, hn, hbn⟩, hb⟩
      exact ⟨by omega, hb⟩
    · rintro ⟨hbN, hb⟩
      exact ⟨⟨b.length, by omega, rfl⟩, hb⟩
  obtain ⟨x, hx⟩ := hX
  have hempty : ([] : Word A) ∈ language X := ⟨x, hx, 0, rfl⟩
  have hex : ∃ k : ℕ, ∃ u ∈ language X, ∃ v ∈ language X,
      (bridges u v).card = k := ⟨_, [], hempty, [], hempty, rfl⟩
  obtain ⟨u, hu, v, hv, hcard⟩ := Nat.find_spec hex
  have hminimal : ∀ a ∈ language X, ∀ c ∈ language X,
      (bridges u v).card ≤ (bridges a c).card := by
    intro a ha c hc
    rw [hcard]
    exact Nat.find_min' hex ⟨a, ha, c, hc, rfl⟩
  obtain ⟨b, _, hbN, hubv⟩ := hN u hu v hv
  have hb : b ∈ bridges u v := mem_bridges.mpr ⟨hbN, hubv⟩
  refine ⟨u ++ b ++ v, hubv, ?_⟩
  intro p q hp hq
  have hpu : p ++ u ∈ language X := by
    apply (language_factorial X).prefix (v := b ++ v)
    simpa only [List.append_assoc] using hp
  have hvq : v ++ q ∈ language X := by
    apply (language_factorial X).suffix (u := u ++ b)
    simpa only [List.append_assoc] using hq
  have hsubset : bridges (p ++ u) (v ++ q) ⊆ bridges u v := by
    intro c hc
    obtain ⟨hcN, hpc⟩ := mem_bridges.mp hc
    refine mem_bridges.mpr ⟨hcN, ?_⟩
    apply language_factorial X (u := u ++ c ++ v)
      (v := (p ++ u) ++ c ++ (v ++ q)) _ hpc
    exact ⟨p, q, by simp only [List.append_assoc]⟩
  have heq : bridges (p ++ u) (v ++ q) = bridges u v :=
    Finset.eq_of_subset_of_card_le hsubset (hminimal (p ++ u) hpu (v ++ q) hvq)
  have hbext : b ∈ bridges (p ++ u) (v ++ q) := by rw [heq]; exact hb
  simpa only [List.append_assoc] using (mem_bridges.mp hbext).2
end BalanceSpecification
