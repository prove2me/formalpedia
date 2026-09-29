-- Prove2me | solution 1 for CannonFloydParry.closure_mapA_mapB_eq_F
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-16T12:34:41.112557+00:00
-- url     : https://prove2.me/submissions/0b5f7b5e-b333-459f-9a62-b27680c945a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_exists_standardDyadicPartition_of_isThompson
import Theorems.Thm_CannonFloydParry_mem_closure_mapA_mapB_of_standardDyadicPartition
import Definitions.Def_CannonFloydParry
import Mathlib

open CannonFloydParry

namespace CFPGenAux

lemma mapA_coe (z : UI) : ((mapA z : UI) : ℝ) = aFun (z : ℝ) := rfl

lemma mapB_coe (z : UI) : ((mapB z : UI) : ℝ) = bFun (z : ℝ) := rfl

lemma zpow_neg_one : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
lemma zpow_zero' : (2 : ℝ) ^ (0 : ℤ) = 1 := by norm_num
lemma zpow_one' : (2 : ℝ) ^ (1 : ℤ) = 2 := by norm_num

/-- `A` is piecewise linear with dyadic breakpoints `1/2, 3/4` and slopes `2^{-1}, 2^0, 2^1`. -/
theorem isThompson_mapA : IsThompson mapA := by
  refine ⟨{1/2, 3/4}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
  · intro x y hxy hB
    have hmem : ∀ b : ℝ, b ∈ ({1/2, 3/4} : Finset ℝ) → b ∉ Set.Ioo (x : ℝ) (y : ℝ) := by
      intro b hb hbm
      have hcap : b ∈ Set.Ioo (x : ℝ) (y : ℝ) ∩ ((({1/2, 3/4} : Finset ℝ) : Set ℝ)) :=
        ⟨hbm, by simpa using hb⟩
      rw [hB] at hcap
      exact hcap
    have h12 : (y : ℝ) ≤ 1/2 ∨ 1/2 ≤ (x : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hmem (1/2) (by simp) ⟨hcon.2, hcon.1⟩
    have h34 : (y : ℝ) ≤ 3/4 ∨ 3/4 ≤ (x : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hmem (3/4) (by simp) ⟨hcon.2, hcon.1⟩
    rcases h12 with h12 | h12
    · refine ⟨-1, 0, fun z hz => ?_⟩
      rw [mapA_coe, aFun_of_mem1 z.2.1 (le_trans hz.2 h12), zpow_neg_one]
      ring
    · rcases h34 with h34 | h34
      · refine ⟨0, -1/4, fun z hz => ?_⟩
        rw [mapA_coe, aFun_of_mem2 (le_trans h12 hz.1) (le_trans hz.2 h34), zpow_zero']
        ring
      · refine ⟨1, -1, fun z hz => ?_⟩
        rw [mapA_coe, aFun_of_mem3 (le_trans h34 hz.1) z.2.2, zpow_one']
        ring

/-- `B` is piecewise linear with dyadic breakpoints `1/2, 3/4, 7/8`. -/
theorem isThompson_mapB : IsThompson mapB := by
  refine ⟨{1/2, 3/4, 7/8}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact ⟨7, 3, by norm_num⟩
  · intro x y hxy hB
    have hmem : ∀ b : ℝ, b ∈ ({1/2, 3/4, 7/8} : Finset ℝ) → b ∉ Set.Ioo (x : ℝ) (y : ℝ) := by
      intro b hb hbm
      have hcap : b ∈ Set.Ioo (x : ℝ) (y : ℝ) ∩ ((({1/2, 3/4, 7/8} : Finset ℝ) : Set ℝ)) :=
        ⟨hbm, by simpa using hb⟩
      rw [hB] at hcap
      exact hcap
    have h12 : (y : ℝ) ≤ 1/2 ∨ 1/2 ≤ (x : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hmem (1/2) (by simp) ⟨hcon.2, hcon.1⟩
    have h34 : (y : ℝ) ≤ 3/4 ∨ 3/4 ≤ (x : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hmem (3/4) (by simp) ⟨hcon.2, hcon.1⟩
    have h78 : (y : ℝ) ≤ 7/8 ∨ 7/8 ≤ (x : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hmem (7/8) (by simp) ⟨hcon.2, hcon.1⟩
    rcases h12 with h12 | h12
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [mapB_coe, bFun_of_le_half (le_trans hz.2 h12), zpow_zero']
      ring
    · rcases h34 with h34 | h34
      · refine ⟨-1, 1/4, fun z hz => ?_⟩
        rw [mapB_coe, bFun_of_mem1 (le_trans h12 hz.1) (le_trans hz.2 h34), zpow_neg_one]
        ring
      · rcases h78 with h78 | h78
        · refine ⟨0, -1/8, fun z hz => ?_⟩
          rw [mapB_coe, bFun_of_mem2 (le_trans h34 hz.1) (le_trans hz.2 h78), zpow_zero']
          ring
        · refine ⟨1, -1, fun z hz => ?_⟩
          rw [mapB_coe, bFun_of_mem3 (le_trans h78 hz.1) z.2.2, zpow_one']
          ring

end CFPGenAux

open CFPGenAux

theorem solution : Subgroup.closure {mapA, mapB} = CannonFloydParry.F := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact CannonFloydParry.mem_F_of_isThompson isThompson_mapA
    · exact CannonFloydParry.mem_F_of_isThompson isThompson_mapB
  · intro g hg
    obtain ⟨n, x, y, hx, hy, hx0, hxn, hy0, hyn, hxs, hys, haff⟩ :=
      CannonFloydParry.exists_standardDyadicPartition_of_isThompson
        (CannonFloydParry.mem_F_iff_isThompson.mp hg)
    exact CannonFloydParry.mem_closure_mapA_mapB_of_standardDyadicPartition
      x y hx hy hx0 hxn hy0 hyn hxs hys haff
