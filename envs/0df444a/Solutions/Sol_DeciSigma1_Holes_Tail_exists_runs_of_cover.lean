-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_runs_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:59.70301+00:00
-- url     : https://prove2.me/submissions/6869ba8c-0a3d-48a0-88ab-46568fab6794

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
public import Theorems.Thm_DeciSigma1_Holes_Periodic_long_factor_in_piece
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_covers_cons
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
theorem _root_.solution (U : Fin k → List α) (i : Fin k) {D : ℕ} :
    ∀ fs : List PeriodicFactor, (∀ f ∈ fs, f.Valid (U i) D) →
    ∃ rs : Finset (RunSpec k), rs.card ≤ fs.length ∧
        (∀ r ∈ rs, r.coordinate = i ∧ IsBoundedRun U D r) ∧
      ∃ X : Finset ℕ, X.card ≤ fs.length * (2 * D) ∧
        ∀ p, Covers fs p → RunCovers rs i p ∨ p ∈ X
  | [], _ => by
    classical
    exact ⟨∅, by simp, by simp, ∅, by simp, fun p h => by simp [Covers] at h⟩
  | f :: fs, hfs => by
    classical
    obtain ⟨rs, hrs1, hrs2, X, hX1, hX2⟩ :=
      solution U i fs (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
    obtain ⟨hp, hpD, hfe, hper⟩ := hfs f List.mem_cons_self
    by_cases hlong : 2 * D ≤ f.stop - f.start
    · obtain ⟨P, hPl, hPs, hPe, hdvd⟩ := long_factor_in_piece U i hp hfe
        (by have := Nat.mul_le_mul_left 2 hpD; omega) hper
      let r : RunSpec k :=
          ⟨i, P.start, P.stop, leastPeriod (((U i).drop f.start).take (f.stop - f.start))⟩
      have hd : leastPeriod (((U i).drop f.start).take (f.stop - f.start)) ≤ D :=
        (Nat.le_of_dvd hp hdvd).trans hpD
      refine ⟨insert r rs, (Finset.card_insert_le _ _).trans (by simp; omega), ?_, X,
        hX1.trans (Nat.mul_le_mul_right _ (by simp)), ?_⟩
      · intro r' hr'
        rcases Finset.mem_insert.mp hr' with rfl | hr'
        · refine ⟨rfl, ?_, hd, by simp only [r]; omega⟩
          have := P.isPeriodicPiece; rw [hPl] at this; exact this
        · exact hrs2 r' hr'
      · intro p hcov
        rcases covers_cons.mp hcov with hf | hcov
        · exact Or.inl ⟨r, Finset.mem_insert_self _ _, rfl, by simp only [r]; omega,
            by simp only [r]; omega⟩
        · rcases hX2 p hcov with h | h
          · exact Or.inl (h.mono (Finset.subset_insert _ _))
          · exact Or.inr h
    · refine ⟨rs, hrs1.trans (by simp), hrs2, Finset.Ico f.start f.stop ∪ X, ?_, ?_⟩
      · calc (Finset.Ico f.start f.stop ∪ X).card ≤ (Finset.Ico f.start f.stop).card + X.card :=
              Finset.card_union_le _ _
          _ ≤ 2 * D + fs.length * (2 * D) := by simp only [Nat.card_Ico]; omega
          _ = (f :: fs).length * (2 * D) := by simp only [List.length_cons]; ring
      · intro p hcov
        rcases covers_cons.mp hcov with hf | hcov
        · exact Or.inr (Finset.mem_union_left _ (Finset.mem_Ico.mpr hf))
        · rcases hX2 p hcov with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_union_right _ h)
end DeciSigma1.Holes.Tail
