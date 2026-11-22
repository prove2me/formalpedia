-- Prove2me | solution 1 for CirclePackingConstants.r_n_sixteen_upper
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-23T14:23:07.875784+00:00
-- url     : https://prove2.me/submissions/f390a991-15d7-417d-93c3-8bf438dd84a3

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_sixteen_unit_square_close_pair

open CirclePackingConstants

-- Reduction of the sixteen-circle optimality upper bound to the universal
-- close-pair fact: any sixteen points in the unit square contain a pair at
-- squared distance at most 1/9.  Normalizing an arbitrary packing and
-- applying that fact forces every packable radius below 1/8.
theorem solution : r_n 16 ≤ (1 : ℝ)/8 := by
  have hd : (0 : ℝ) < 1 / 3 := by norm_num
  have hdsq : ((1 / 3 : ℝ)) ^ 2 = 1 / 9 := by norm_num
  have hpack0 : Packable 16 0 := by
    refine ⟨le_rfl, by norm_num, (fun _ => (0, 0)), ?_, ?_⟩
    · intro i
      exact ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩
    · intro i j _
      unfold sqDist
      norm_num
  show sSup {r : ℝ | Packable 16 r} ≤ _
  apply csSup_le ⟨0, hpack0⟩
  intro r hr
  obtain ⟨hr0, hr1, p, hmem, hsep⟩ := hr
  have hne : r ≠ 1 / 2 := by
    rintro rfl
    have hall : ∀ i, p i = (1 / 2, 1 / 2) := by
      intro i
      obtain ⟨h1, h2, h3, h4⟩ := hmem i
      apply Prod.ext <;> simp only
      · have h2' : (p i).1 ≤ (1 / 2 : ℝ) := by linarith [h2]
        exact le_antisymm h2' h1
      · have h4' : (p i).2 ≤ (1 / 2 : ℝ) := by linarith [h4]
        exact le_antisymm h4' h3
    have h01 : (0 : Fin 16) ≠ 1 := by decide
    have hbad := hsep 0 1 h01
    rw [hall 0, hall 1] at hbad
    simp only [sqDist] at hbad
    norm_num at hbad
  have hs : (0 : ℝ) < 1 - 2 * r := by
    have : r < 1 / 2 := lt_of_le_of_ne hr1 hne
    linarith
  have hsne : (1 : ℝ) - 2 * r ≠ 0 := ne_of_gt hs
  set q : Fin 16 → Point := fun i => (((p i).1 - r) / (1 - 2 * r), ((p i).2 - r) / (1 - 2 * r)) with hq
  have hqmem : ∀ i, 0 ≤ (q i).1 ∧ (q i).1 ≤ 1 ∧ 0 ≤ (q i).2 ∧ (q i).2 ≤ 1 := by
    intro i
    obtain ⟨h1, h2, h3, h4⟩ := hmem i
    simp only [hq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr h1) (le_of_lt hs)
    · rw [div_le_one hs]
      linarith
    · exact div_nonneg (sub_nonneg.mpr h3) (le_of_lt hs)
    · rw [div_le_one hs]
      linarith
  obtain ⟨i, j, hij, hclose⟩ :=
    CirclePackingConstants.sixteen_unit_square_close_pair q hqmem
  have hclose' : sqDist (q i) (q j) ≤ (1 : ℝ)/9 := by simpa using hclose
  have hsepi := hsep i j hij
  have hscale : sqDist (p i) (p j) = (1 - 2 * r) ^ 2 * sqDist (q i) (q j) := by
    simp only [sqDist, hq]
    field_simp
    ring
  have hkey : (2 * r) ^ 2 ≤ ((1 - 2 * r) * (1 / 3)) ^ 2 := by
    calc (2 * r) ^ 2 ≤ sqDist (p i) (p j) := hsepi
      _ = (1 - 2 * r) ^ 2 * sqDist (q i) (q j) := hscale
      _ ≤ (1 - 2 * r) ^ 2 * (1 / 9) := by
          apply mul_le_mul_of_nonneg_left hclose' (sq_nonneg _)
      _ = ((1 - 2 * r) * (1 / 3)) ^ 2 := by
          rw [mul_pow, hdsq]
  have hnn1 : (0 : ℝ) ≤ 2 * r := by linarith
  have hnn2 : (0 : ℝ) ≤ (1 - 2 * r) * (1 / 3) :=
    mul_nonneg (le_of_lt hs) (le_of_lt hd)
  have hlin : 2 * r ≤ (1 - 2 * r) * (1 / 3) := by
    have h1 : Real.sqrt ((2 * r) ^ 2) ≤ Real.sqrt (((1 - 2 * r) * (1 / 3)) ^ 2) :=
      Real.sqrt_le_sqrt hkey
    rw [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at h1
    exact h1
  linarith
