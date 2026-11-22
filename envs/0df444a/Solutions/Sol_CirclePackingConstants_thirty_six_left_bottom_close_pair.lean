-- Prove2me | solution 1 for CirclePackingConstants.thirty_six_left_bottom_close_pair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T14:42:28.415426+00:00
-- url     : https://prove2.me/submissions/dd9e2198-8f1b-4996-886d-24e7c5694ba1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_thirty_six_three_sides_close_pair

open CirclePackingConstants

theorem solution :
    ∀ p : Fin 36 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      (∃ i, (p i).1 = 0) →
      (∃ j, (p j).2 = 0) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (1 : ℝ) / 25 := by
  intro p hp hl hb
  classical
  let S : Finset ℝ := Finset.univ.image (fun i : Fin 36 => max (p i).1 (p i).2)
  have hS : S.Nonempty := ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  let M := S.max' hS
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (Finset.max'_mem S hS)
  have hbound (i : Fin 36) : (p i).1 ≤ M ∧ (p i).2 ≤ M := by
    have h : max (p i).1 (p i).2 ≤ M :=
      Finset.le_max' S _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
  have hM : M ≤ 1 := by
    change max (p k).1 (p k).2 = M at hk
    rw [← hk]
    exact max_le (hp k).2.1 (hp k).2.2.2
  by_cases hpos : 0 < M
  · let q : Fin 36 → Point := fun i => ((p i).1 / M, (p i).2 / M)
    have hq (i : Fin 36) : 0 ≤ (q i).1 ∧ (q i).1 ≤ 1 ∧
        0 ≤ (q i).2 ∧ (q i).2 ≤ 1 :=
      ⟨div_nonneg (hp i).1 hpos.le, (div_le_one hpos).mpr (hbound i).1,
        div_nonneg (hp i).2.2.1 hpos.le, (div_le_one hpos).mpr (hbound i).2⟩
    obtain ⟨a, ha⟩ := hl
    obtain ⟨b, hb⟩ := hb
    have hside : (∃ i, (q i).1 = 1) ∨ (∃ i, (q i).2 = 1) := by
      rcases le_total (p k).1 (p k).2 with h | h
      · right
        refine ⟨k, ?_⟩
        change (p k).2 / M = 1
        rw [max_eq_right h] at hk
        rw [hk, div_self hpos.ne']
      · left
        refine ⟨k, ?_⟩
        change (p k).1 / M = 1
        rw [max_eq_left h] at hk
        rw [hk, div_self hpos.ne']
    obtain ⟨i,j,hij,hd⟩ := thirty_six_three_sides_close_pair q hq
      ⟨a, by simp [q, ha]⟩ ⟨b, by simp [q, hb]⟩ hside
    refine ⟨i,j,hij,?_⟩
    have he : sqDist (p i) (p j) = M ^ 2 * sqDist (q i) (q j) := by
      unfold sqDist q
      field_simp
      <;> ring
    rw [he]
    calc
      _ ≤ M ^ 2 * (1 / 25 : ℝ) := mul_le_mul_of_nonneg_left hd (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hM)]
  · have hz (i : Fin 36) : p i = (0, 0) :=
      Prod.ext (le_antisymm ((hbound i).1.trans (le_of_not_gt hpos)) (hp i).1)
        (le_antisymm ((hbound i).2.trans (le_of_not_gt hpos)) (hp i).2.2.1)
    exact ⟨0, 1, by decide, by rw [hz 0, hz 1]; norm_num [sqDist]⟩
