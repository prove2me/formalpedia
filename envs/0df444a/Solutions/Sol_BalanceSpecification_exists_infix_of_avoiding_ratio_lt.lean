-- Prove2me | solution 1 for BalanceSpecification.exists_infix_of_avoiding_ratio_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:32.438475+00:00
-- url     : https://prove2.me/submissions/44d7c31a-1166-4916-91fb-5d3d73fa872a

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution {v : Word A} {N : ℕ}
    {s : Finset (Word A)} (hs : s ⊆ wordFinset L N)
    (hsmall : (wordCount (avoidingLanguage L v) N : ℝ) / wordCount L N <
      (s.card : ℝ) / wordCount L N) :
    ∃ w ∈ s, v <:+: w := by
  classical
  by_contra hnone
  have hsub : s ⊆ wordFinset (avoidingLanguage L v) N := by
    intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp (hs hw)
    exact mem_wordFinset.mpr ⟨⟨hwL, fun hvw => hnone ⟨w, hw, hvw⟩⟩, hwlen⟩
  have hcard : (s.card : ℝ) ≤ wordCount (avoidingLanguage L v) N := by
    exact_mod_cast Finset.card_le_card hsub
  exact (not_lt_of_ge (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _))) hsmall
end BalanceSpecification
