-- Prove2me | solution 1 for BalanceSpecification.mem_languageShift_of_arbitrary_contexts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:31.972797+00:00
-- url     : https://prove2.me/submissions/63d72dba-a16a-4bae-8bfb-1322c3687748

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_block_isInfix_block
public import Theorems.Thm_BalanceSpecification_exists_configuration_with_block
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_isClosed_block_mem
public import Theorems.Thm_BalanceSpecification_block_subword
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_isClosed_wordCylinder
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_languageShift_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution [Nonempty A]
    {L : Set (Word A)} (hL : IsFactorial L) {w : Word A}
    (hw : ∀ M : ℕ, ∃ p q : Word A,
      M ≤ p.length ∧ M ≤ q.length ∧ p ++ w ++ q ∈ L) :
    w ∈ language (languageShift L) := by
  classical
  let C : ℕ → Set (Configuration A) := fun M =>
    {x | block x 0 w.length = w ∧ block x (-(M : ℤ)) (w.length + 2 * M) ∈ L}
  have hCclosed (M : ℕ) : IsClosed (C M) :=
    (isClosed_wordCylinder w 0).inter (isClosed_block_mem L _ _)
  have hCnonempty (M : ℕ) : (C M).Nonempty := by
    obtain ⟨p, q, hp, hq, hpwq⟩ := hw M
    obtain ⟨x, hx⟩ := exists_configuration_with_block (p ++ w ++ q) (-(p.length : ℤ))
    refine ⟨x, ?_, ?_⟩
    · have hh := block_subword x (-(p.length : ℤ)) p w q hx
      simpa only [neg_add_cancel] using hh
    · have hsub := block_isInfix_block x (-(M : ℤ)) (-(p.length : ℤ))
        (w.length + 2 * M) (p ++ w ++ q).length (by omega) (by
          simp only [List.length_append, Nat.cast_add]
          omega)
      rw [hx] at hsub
      exact hL hsub hpwq
  have hCanti (M : ℕ) : C (M + 1) ⊆ C M := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    apply hL (block_isInfix_block x (-(M : ℤ)) (-((M + 1 : ℕ) : ℤ))
      (w.length + 2 * M) (w.length + 2 * (M + 1)) (by omega) (by omega)) hx.2
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hCanti hCnonempty (hCclosed 0).isCompact hCclosed
  have hxM : ∀ M, x ∈ C M := Set.mem_iInter.mp hx
  have hxshift : x ∈ (languageShift L).carrier := by
    apply mem_languageShift_iff.mpr
    intro k n
    let M := k.natAbs + n
    have hu : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
    have hl : -k ≤ (k.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -k))
    apply hL (block_isInfix_block x k (-(M : ℤ)) n (w.length + 2 * M)
      (by dsimp only [M]; omega) (by dsimp only [M]; omega)) (hxM M).2
  exact ⟨x, hxshift, 0, (hxM 0).1⟩
end BalanceSpecification
