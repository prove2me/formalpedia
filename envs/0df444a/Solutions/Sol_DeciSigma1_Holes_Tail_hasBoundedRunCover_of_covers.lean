-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.hasBoundedRunCover_of_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:05:08.239962+00:00
-- url     : https://prove2.me/submissions/6e00f81f-f1a6-4c83-8c10-a58669eae686

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_runs_of_cover
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_uncoveredTailPositions_le
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
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
theorem _root_.solution
    (M : StructuralReader α S k)
    (U : Fin k → List α) {P D T : ℕ}
    (h : ∀ i, M.Immortal (M.endState U i) → PeriodicCover (U i) (M.firstRejection U i) P D T) :
    HasBoundedRunCover M U (k * P) D (k * (T + P * (2 * D))) := by
  classical
  have h2 : ∀ i, ∃ rs : Finset (RunSpec k), rs.card ≤ P ∧
      (∀ r ∈ rs, r.coordinate = i ∧ IsBoundedRun U D r) ∧
      (M.Immortal (M.endState U i) → ∀ runs : Finset (RunSpec k), rs ⊆ runs →
        (uncoveredTailPositions M U runs i).card ≤ T + P * (2 * D)) := by
    intro i
    by_cases him : M.Immortal (M.endState U i)
    · obtain ⟨fs, hfs1, hfs2, hfs3⟩ := h i him
      obtain ⟨rs, hrs1, hrs2, X, hX1, hX2⟩ := exists_runs_of_cover U i fs hfs2
      refine ⟨rs, hrs1.trans hfs1, hrs2, fun _ runs hsub => ?_⟩
      have := card_uncoveredTailPositions_le M U hsub i hX2
      have := Nat.mul_le_mul_right (2 * D) hfs1
      omega
    · exact ⟨∅, by simp, by simp, fun h => absurd h him⟩
  choose rs hrs1 hrs2 hrs3 using h2
  refine ⟨Finset.univ.biUnion rs, ?_, ?_, ?_⟩
  · calc (Finset.univ.biUnion rs).card ≤ ∑ i, (rs i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin k, P := Finset.sum_le_sum fun i _ => hrs1 i
      _ = k * P := by simp
  · intro r hr
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hr
    exact (hrs2 i r hi).2
  · calc ∑ i, (if M.Immortal (M.endState U i) then
            (uncoveredTailPositions M U (Finset.univ.biUnion rs) i).card else 0)
        ≤ ∑ _i : Fin k, (T + P * (2 * D)) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs with him
          · exact hrs3 i him _ (Finset.subset_biUnion_of_mem rs (Finset.mem_univ i))
          · exact Nat.zero_le _
      _ = k * (T + P * (2 * D)) := by simp
end DeciSigma1.Holes.Tail
