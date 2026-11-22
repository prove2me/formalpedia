-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.card_uncoveredTailPositions_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:00.264069+00:00
-- url     : https://prove2.me/submissions/98b4373f-9f43-4ed2-a690-2e3dfa0b089e

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Theorems.Thm_DeciSigma1_Holes_Tail_RunCovers_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (M : StructuralReader α S k) (U : Fin k → List α)
    {runs rs : Finset (RunSpec k)}
    (hsub : rs ⊆ runs) (i : Fin k) {fs : List PeriodicFactor} {X : Finset ℕ}
    (hX : ∀ p, Covers fs p → RunCovers rs i p ∨ p ∈ X) :
    (uncoveredTailPositions M U runs i).card ≤
        (uncoveredPositions fs (M.firstRejection U i) (U i).length).card + X.card := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro p hp
  simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico] at hp
  by_cases hc : Covers fs p
  · rcases hX p hc with h | h
    · exact absurd (h.mono hsub) hp.2
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp [uncoveredPositions, hp.1, hc])
end DeciSigma1.Holes.Tail
