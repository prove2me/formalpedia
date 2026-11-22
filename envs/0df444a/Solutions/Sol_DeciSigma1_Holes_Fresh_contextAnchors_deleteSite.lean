-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.contextAnchors_deleteSite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:54.358+00:00
-- url     : https://prove2.me/submissions/308c50ca-4969-491b-beed-1b68ab524a8b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_append_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_crossing_length_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_deleteSite_of_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_deleteSite_of_ge
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_add_delta
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_deleteSite
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_marker_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
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
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {x : List α} {c δ : ℕ}
    (hS : ValidDeletionSite W t x c δ) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) (e : ℕ) :
    e ∈ contextAnchors W r (x.take c ++ x.drop (c + δ)) ↔
      (e ≤ c ∧ e ∈ contextAnchors W r x) ∨ (c ≤ e ∧ e + δ ∈ contextAnchors W r x) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hcx : c + δ ≤ x.length := hS.le_len
  have hlen := length_deleteSite (x := x) hcx
  simp only [mem_contextAnchors_succ]
  constructor
  · rintro ⟨heL, m, hm, hs⟩
    by_cases hec : e ≤ c
    · left
      rw [take_deleteSite_of_le (by omega) hec] at hs
      exact ⟨hec, by omega, m, hm, hs⟩
    · right
      refine ⟨by omega, by omega, m, hm, ?_⟩
      rw [take_deleteSite_of_ge (by omega) (by omega)] at hs
      rw [take_add_delta (by omega : c ≤ e)]
      set R := (x.drop (c + δ)).take (e - c) with hR
      have hRl : R.length = e - c := by simp [hR]; omega
      by_cases hμR : (marker W (r + 1) m).length ≤ e - c
      · exact (List.suffix_of_suffix_length_le hs (List.suffix_append _ _) (by omega)).trans
          (List.suffix_append _ _)
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · have : r = 0 := by omega
          subst this
          have : (marker W (0 + 1) m).length = 1 := length_marker_one hm
          omega
        obtain ⟨m0, hm0, hτ⟩ := hS.anchor ht
        have hτ'' : marker W t m0 <:+ (x.take c ++ x.drop (c + δ)).take c := by
          rwa [take_deleteSite_of_le (by omega) le_rfl]
        have hs' : marker W (r + 1) m <:+ (x.take c ++ x.drop (c + δ)).take e := by
          rwa [take_deleteSite_of_ge (by omega) (by omega)]
        have hcr := crossing_length_le ht hr hm hm0 hτ'' hs' (by omega) (by omega)
        have h1 : marker W (r + 1) m <:+ marker W t m0 ++ R :=
          List.suffix_of_suffix_length_le hs (suffix_append_right hτ R) (by simp; omega)
        have hτ2 := ((hS.types t ht le_rfl m0 hm0).mp hτ)
        exact h1.trans (suffix_append_right hτ2 R)
  · rintro (⟨hec, heL, m, hm, hs⟩ | ⟨hce, heL, m, hm, hs⟩)
    · refine ⟨by omega, m, hm, ?_⟩
      rwa [take_deleteSite_of_le (by omega) hec]
    · refine ⟨by omega, m, hm, ?_⟩
      rw [take_deleteSite_of_ge (by omega) hce]
      rw [take_add_delta hce] at hs
      set R := (x.drop (c + δ)).take (e - c) with hR
      have hRl : R.length = e - c := by simp [hR]; omega
      by_cases hμR : (marker W (r + 1) m).length ≤ e - c
      · exact (List.suffix_of_suffix_length_le hs (List.suffix_append _ _) (by omega)).trans
          (List.suffix_append _ _)
      · rcases Nat.eq_or_lt_of_le hce with hceq | hcl
        · -- the marker ends exactly at the right cut `c + δ`
          subst hceq
          have hR0 : R = [] := by simp [hR]
          rw [hR0, List.append_nil] at hs ⊢
          rcases Nat.lt_or_ge (r + 1) (t + 1) with hrt | hrt
          · exact (hS.types (r + 1) (by omega) (by omega) m hm).mpr hs
          · have : r = t := by omega
            subst this
            exact absurd hs (hS.no_upper_marker m hm)
        · rcases Nat.eq_zero_or_pos t with rfl | ht
          · have : r = 0 := by omega
            subst this
            have : (marker W (0 + 1) m).length = 1 := length_marker_one hm
            omega
          obtain ⟨m0, hm0, hτ⟩ := hS.anchor ht
          have hτ2 := ((hS.types t ht le_rfl m0 hm0).mp hτ)
          have hs' : marker W (r + 1) m <:+ x.take (e + δ) := by
            rw [take_add_delta hce]; exact hs
          have hcr := crossing_length_le ht hr hm hm0 hτ2 hs' (by omega) (by omega)
          have h1 : marker W (r + 1) m <:+ marker W t m0 ++ R :=
            List.suffix_of_suffix_length_le hs (suffix_append_right hτ2 R) (by simp; omega)
          exact h1.trans (suffix_append_right hτ R)
end DeciSigma1.Holes.Fresh
