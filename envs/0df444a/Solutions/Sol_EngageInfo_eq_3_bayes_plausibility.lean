-- Prove2me | solution 1 for EngageInfo.eq_3_bayes_plausibility
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:21:18.478902+00:00
-- url     : https://prove2.me/submissions/4c9e3f6d-b5bc-4ca1-88e0-b36bda3ad3ea

import Definitions.Def_EngageInfo_designs

namespace Aux_EngageInfo_eq_3
open EngageInfo

lemma probH_mem (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) {π : ℝ × ℝ} (hπ : π ∈ designs) :
    probH a0 π ∈ Set.Icc (0 : ℝ) 1 := by
  rcases ha0 with ⟨h0, h1⟩
  rcases hπ with ⟨hπ1_0, hπ1_1, hπ2_0, hπ2_1, _⟩
  unfold probH
  exact ⟨by nlinarith, by nlinarith⟩

lemma probL_mem (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) {π : ℝ × ℝ} (hπ : π ∈ designs) :
    probL a0 π ∈ Set.Icc (0 : ℝ) 1 := by
  rcases ha0 with ⟨h0, h1⟩
  rcases hπ with ⟨hπ1_0, hπ1_1, hπ2_0, hπ2_1, _⟩
  unfold probL
  exact ⟨by nlinarith, by nlinarith⟩

lemma prob_sum_one (a0 : ℝ) (π : ℝ × ℝ) : probH a0 π + probL a0 π = 1 := by
  unfold probH probL
  ring

lemma postL_bounds (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) {π : ℝ × ℝ} (hπ : π ∈ designs) :
    0 ≤ postL a0 π ∧ postL a0 π ≤ a0 := by
  have hLmem := probL_mem a0 ha0 hπ
  rcases ha0 with ⟨h0, h1⟩
  rcases hπ with ⟨hπ1_0, hπ1_1, hπ2_0, hπ2_1, hsum⟩
  unfold postL
  split_ifs with hL0
  · exact ⟨h0.le, le_rfl⟩
  · have hLpos : 0 < probL a0 π := lt_of_le_of_ne hLmem.1 (Ne.symm hL0)
    refine ⟨div_nonneg (by nlinarith) hLpos.le, ?_⟩
    rw [div_le_iff₀ hLpos]
    unfold probL
    have hid : a0 * (a0 * (1 - π.1) + (1 - a0) * π.2) - a0 * (1 - π.1) =
        a0 * (1 - a0) * (π.1 + π.2 - 1) := by ring
    have hprod : 0 ≤ a0 * (1 - a0) * (π.1 + π.2 - 1) :=
      mul_nonneg (mul_nonneg h0.le (by linarith)) (by linarith)
    linarith

lemma postH_bounds (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) {π : ℝ × ℝ} (hπ : π ∈ designs) :
    a0 ≤ postH a0 π ∧ postH a0 π ≤ 1 := by
  have hHmem := probH_mem a0 ha0 hπ
  rcases ha0 with ⟨h0, h1⟩
  rcases hπ with ⟨hπ1_0, hπ1_1, hπ2_0, hπ2_1, hsum⟩
  unfold postH
  split_ifs with hH0
  · exact ⟨le_rfl, h1.le⟩
  · have hHpos : 0 < probH a0 π := lt_of_le_of_ne hHmem.1 (Ne.symm hH0)
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hHpos]
      unfold probH
      have hid : a0 * π.1 - a0 * (a0 * π.1 + (1 - a0) * (1 - π.2)) =
          a0 * (1 - a0) * (π.1 + π.2 - 1) := by ring
      have hprod : 0 ≤ a0 * (1 - a0) * (π.1 + π.2 - 1) :=
        mul_nonneg (mul_nonneg h0.le (by linarith)) (by linarith)
      linarith
    · rw [div_le_iff₀ hHpos]
      unfold probH
      nlinarith

lemma mul_postH (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) {π : ℝ × ℝ} (hπ : π ∈ designs) :
    probH a0 π * postH a0 π = a0 * π.1 := by
  rcases ha0 with ⟨h0, h1⟩
  rcases hπ with ⟨hπ1_0, hπ1_1, hπ2_0, hπ2_1, _⟩
  unfold postH
  split_ifs with hH0
  · rw [hH0, zero_mul]
    unfold probH at hH0
    have ht1 : 0 ≤ a0 * π.1 := mul_nonneg h0.le hπ1_0
    have ht2 : 0 ≤ (1 - a0) * (1 - π.2) := mul_nonneg (by linarith) (by linarith)
    linarith
  · exact mul_div_cancel₀ _ hH0

lemma mul_postL (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) {π : ℝ × ℝ} (hπ : π ∈ designs) :
    probL a0 π * postL a0 π = a0 * (1 - π.1) := by
  rcases ha0 with ⟨h0, h1⟩
  rcases hπ with ⟨hπ1_0, hπ1_1, hπ2_0, hπ2_1, _⟩
  unfold postL
  split_ifs with hL0
  · rw [hL0, zero_mul]
    unfold probL at hL0
    have ht1 : 0 ≤ a0 * (1 - π.1) := mul_nonneg h0.le (by linarith)
    have ht2 : 0 ≤ (1 - a0) * π.2 := mul_nonneg (by linarith) hπ2_0
    linarith
  · exact mul_div_cancel₀ _ hL0

end Aux_EngageInfo_eq_3

open EngageInfo Aux_EngageInfo_eq_3

theorem solution (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ π ∈ designs,
      0 ≤ postL a0 π ∧ postL a0 π ≤ a0 ∧ a0 ≤ postH a0 π ∧ postH a0 π ≤ 1 ∧
      probH a0 π ∈ Set.Icc (0 : ℝ) 1 ∧ probL a0 π ∈ Set.Icc (0 : ℝ) 1 ∧
      probH a0 π + probL a0 π = 1 ∧
      probH a0 π * postH a0 π + probL a0 π * postL a0 π = a0) ∧
    (∀ a b : ℝ, 0 ≤ a → a < a0 → a0 < b → b ≤ 1 →
      designOf a0 a b ∈ designs ∧ Induces a0 (designOf a0 a b) a b ∧
      probH a0 (designOf a0 a b) = (a0 - a) / (b - a)) := by
  refine ⟨fun π hπ => ?_, fun a b ha ha0_gt hb_gt hb1 => ?_⟩
  · obtain ⟨hL0, hLa0⟩ := postL_bounds a0 ha0 hπ
    obtain ⟨hHa0, hH1⟩ := postH_bounds a0 ha0 hπ
    refine ⟨hL0, hLa0, hHa0, hH1, probH_mem a0 ha0 hπ, probL_mem a0 ha0 hπ,
      prob_sum_one a0 π, ?_⟩
    rw [mul_postH a0 ha0 hπ, mul_postL a0 ha0 hπ]
    ring
  · rcases ha0 with ⟨ha0_pos, ha0_lt1⟩
    have hba_pos : 0 < b - a := by linarith
    have h1a0_pos : 0 < 1 - a0 := by linarith
    have hd1_pos : 0 < a0 * (b - a) := mul_pos ha0_pos hba_pos
    have hd2_pos : 0 < (1 - a0) * (b - a) := mul_pos h1a0_pos hba_pos
    have hmem : designOf a0 a b ∈ designs := by
      unfold designs designOf
      simp only [Set.mem_setOf_eq]
      refine ⟨div_nonneg (by nlinarith) hd1_pos.le,
        (div_le_iff₀ hd1_pos).mpr (by nlinarith),
        div_nonneg (by nlinarith) hd2_pos.le,
        (div_le_iff₀ hd2_pos).mpr (by nlinarith), ?_⟩
      have hne1 : a0 ≠ 0 := ha0_pos.ne'
      have hne2 : 1 - a0 ≠ 0 := h1a0_pos.ne'
      have hne3 : b - a ≠ 0 := hba_pos.ne'
      rw [← sub_nonneg]
      have hid : b * (a0 - a) / (a0 * (b - a)) + (b - a0) * (1 - a) / ((1 - a0) * (b - a)) - 1 =
          (b - a0) * (a0 - a) / (a0 * (1 - a0) * (b - a)) := by
        field_simp; ring
      rw [hid]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith))
        (mul_pos (mul_pos ha0_pos h1a0_pos) hba_pos).le
    have hpH : probH a0 (designOf a0 a b) = (a0 - a) / (b - a) := by
      unfold probH designOf
      have hne1 : a0 ≠ 0 := ha0_pos.ne'
      have hne2 : 1 - a0 ≠ 0 := h1a0_pos.ne'
      have hne3 : b - a ≠ 0 := hba_pos.ne'
      field_simp
      ring
    have hpL : probL a0 (designOf a0 a b) = (b - a0) / (b - a) := by
      have hsum := prob_sum_one a0 (designOf a0 a b)
      rw [hpH] at hsum
      have hne3 : b - a ≠ 0 := hba_pos.ne'
      have : probL a0 (designOf a0 a b) = 1 - (a0 - a) / (b - a) := by linarith
      rw [this]
      field_simp
      ring
    have hpH_pos : 0 < probH a0 (designOf a0 a b) := by
      rw [hpH]; exact div_pos (by linarith) hba_pos
    have hpL_pos : 0 < probL a0 (designOf a0 a b) := by
      rw [hpL]; exact div_pos (by linarith) hba_pos
    refine ⟨hmem, ⟨?_, ?_⟩, hpH⟩
    · unfold postL
      rw [if_neg hpL_pos.ne', hpL]
      unfold designOf
      have hne1 : a0 ≠ 0 := ha0_pos.ne'
      have hne3 : b - a ≠ 0 := hba_pos.ne'
      have hne4 : b - a0 ≠ 0 := (by linarith : 0 < b - a0).ne'
      field_simp
      ring
    · unfold postH
      rw [if_neg hpH_pos.ne', hpH]
      unfold designOf
      have hne1 : a0 ≠ 0 := ha0_pos.ne'
      have hne3 : b - a ≠ 0 := hba_pos.ne'
      have hne5 : a0 - a ≠ 0 := (by linarith : 0 < a0 - a).ne'
      field_simp
