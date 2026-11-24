-- Prove2me | solution 1 for BalanceSpecification.finite_carrier_of_bounded_wordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:25.819815+00:00
-- url     : https://prove2.me/submissions/a9cbfd44-07b3-40b9-bd5f-616809e124c9

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_exists_injective_centered_block
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution
    (h : ∃ C : ℕ, ∀ n, wordCount (language X) n ≤ C) : X.carrier.Finite := by
  classical
  obtain ⟨C, hC⟩ := h
  by_contra hinfinite
  obtain ⟨s, hsX, hscard⟩ := Set.Infinite.exists_subset_card_eq hinfinite (C + 1)
  obtain ⟨M, hM⟩ := exists_injective_centered_block s
  have hcard : s.card ≤ wordCount (language X) (2 * M + 1) := by
    apply Finset.card_le_card_of_injOn (fun x => block x (-(M : ℤ)) (2 * M + 1))
    · intro x hx
      exact mem_wordFinset.mpr ⟨block_mem_language (hsX hx) _ _, length_block _ _ _⟩
    · exact hM
  have := hC (2 * M + 1)
  omega
end BalanceSpecification
