-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.contextAnchors_deleteSites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:52.899809+00:00
-- url     : https://prove2.me/submissions/367b6f53-be43-40a7-af96-cf06df717a17

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_ValidDeletionSite_of_take
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_deleteSite_of_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_deleteSite
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_deleteSite
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Holes_Fresh_sitePositions_insert
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_deletePositions_union_Ico
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_union_Ico_of_ge
public import Theorems.Thm_DeciSigma1_Words_retainedCount_union_Ico_of_le
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ t + 1) (cs : Finset ℕ) : ∀ {x : List α}, StrictlySeparated δ cs →
    (∀ c ∈ cs, ValidDeletionSite W t x c δ) → ∀ e,
      e ∈ contextAnchors W r (deletePositions x (sitePositions δ cs)) ↔
        ∃ p ∈ contextAnchors W r x, Retained δ cs p ∧ retainedCount (sitePositions δ cs) p = e := by
  induction cs using Finset.induction_on_max with
  | empty =>
    intro x _ _ e
    simp only [sitePositions, Finset.biUnion_empty, deletePositions_empty, retainedCount_empty,
      Retained, Finset.notMem_empty, false_imp_iff, implies_true, true_and, exists_eq_right]
  | insert c cs hmax ih =>
    intro x hsep hok e
    have hc := hok c (mem_insert_self ..)
    have hcx := hc.le_len
    have hlt : ∀ c2 ∈ cs, c2 + δ < c := fun c2 h2 =>
      hsep c2 (mem_insert_of_mem h2) c (mem_insert_self ..) (hmax c2 h2)
    have hD : ∀ p ∈ sitePositions δ cs, p < c := fun p hp => by
      obtain ⟨c2, h2, -, h3⟩ := mem_sitePositions.mp hp
      have := hlt c2 h2; omega
    have hok' : ∀ c2 ∈ cs, ValidDeletionSite W t (x.take c ++ x.drop (c + δ)) c2 δ := by
      intro c2 hc2
      have h2 := hlt c2 hc2
      refine (hok c2 (mem_insert_of_mem hc2)).of_take (p := c)
        (take_deleteSite_of_le (by omega) le_rfl) h2.le ?_
      rw [length_deleteSite hcx]; omega
    rw [sitePositions_insert, deletePositions_union_Ico x hD (by omega),
      ih (fun a ha b hb => hsep a (mem_insert_of_mem ha) b (mem_insert_of_mem hb)) hok' e]
    constructor
    · rintro ⟨p', hp', hret, hk⟩
      rcases (contextAnchors_deleteSite hc hr1 hr p').mp hp' with ⟨hpc, hpx⟩ | ⟨hcp, hpx⟩
      · refine ⟨p', hpx, fun c2 hc2 => ?_, by rwa [retainedCount_union_Ico_of_le hpc]⟩
        rcases mem_insert.mp hc2 with rfl | hc2
        · omega
        · exact hret c2 hc2
      · refine ⟨p' + δ, hpx, fun c2 hc2 => ?_, ?_⟩
        · rcases mem_insert.mp hc2 with rfl | hc2
          · omega
          · have := hlt c2 hc2; omega
        · rwa [retainedCount_union_Ico_of_ge hD (by omega), Nat.add_sub_cancel]
    · rintro ⟨p, hp, hret, hk⟩
      have hretc := hret c (mem_insert_self ..)
      by_cases h : p ≤ c
      · exact ⟨p, (contextAnchors_deleteSite hc hr1 hr p).mpr (Or.inl ⟨h, hp⟩),
          fun c2 hc2 => hret c2 (mem_insert_of_mem hc2),
          by rwa [← retainedCount_union_Ico_of_le h]⟩
      · refine ⟨p - δ, (contextAnchors_deleteSite hc hr1 hr _).mpr
          (Or.inr ⟨by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩), ?_,
          by rwa [← retainedCount_union_Ico_of_ge hD (by omega)]⟩
        intro c2 hc2 ⟨h1, h2⟩
        have := hlt c2 hc2; omega
end DeciSigma1.Holes.Fresh
