-- Prove2me | solution 1 for CirclePackingConstants.r_n_eight_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T07:27:59.419384+00:00
-- url     : https://prove2.me/submissions/670ad3e2-acf0-45a9-bd10-edba2d5b55ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_eight_unit_square_close_pair

open CirclePackingConstants

-- Reduction of the eight-circle optimality upper bound to the universal
-- close-pair fact: any eight points in the unit square contain a pair at
-- squared distance at most 2 - sqrt 3.  Normalizing an arbitrary packing and
-- applying that fact forces every packable radius below d/(2(1+d)) with
-- d = sqrt (2 - sqrt 3).
theorem solution : r_n 8 ≤ (Real.sqrt (2 - Real.sqrt 3)) / (2 * (1 + Real.sqrt (2 - Real.sqrt 3))) := by
  have h3nn : (0 : ℝ) ≤ 3 := by norm_num
  have hsqrt3_lt : Real.sqrt 3 < 2 := by
    have h1 : Real.sqrt 3 < Real.sqrt 4 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h2 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    linarith
  have h2sub : (0 : ℝ) < 2 - Real.sqrt 3 := by linarith
  have hd : (0 : ℝ) < Real.sqrt (2 - Real.sqrt 3) := Real.sqrt_pos.mpr h2sub
  have hdsq : (Real.sqrt (2 - Real.sqrt 3)) ^ 2 = 2 - Real.sqrt 3 :=
    Real.sq_sqrt (le_of_lt h2sub)
  have hpack0 : Packable 8 0 := by
    refine ⟨le_rfl, by norm_num, (fun _ => (0, 0)), ?_, ?_⟩
    · intro i
      exact ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩
    · intro i j _
      unfold sqDist
      norm_num
  show sSup {r : ℝ | Packable 8 r} ≤ _
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
    have h01 : (0 : Fin 8) ≠ 1 := by decide
    have hbad := hsep 0 1 h01
    rw [hall 0, hall 1] at hbad
    simp only [sqDist] at hbad
    norm_num at hbad
  have hs : (0 : ℝ) < 1 - 2 * r := by
    have : r < 1 / 2 := lt_of_le_of_ne hr1 hne
    linarith
  have hsne : (1 : ℝ) - 2 * r ≠ 0 := ne_of_gt hs
  set q : Fin 8 → Point := fun i => (((p i).1 - r) / (1 - 2 * r), ((p i).2 - r) / (1 - 2 * r)) with hq
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
    CirclePackingConstants.eight_unit_square_close_pair q hqmem
  have hsepi := hsep i j hij
  have hscale : sqDist (p i) (p j) = (1 - 2 * r) ^ 2 * sqDist (q i) (q j) := by
    simp only [sqDist, hq]
    field_simp
    ring
  have hkey : (2 * r) ^ 2 ≤ ((1 - 2 * r) * (Real.sqrt (2 - Real.sqrt 3))) ^ 2 := by
    calc (2 * r) ^ 2 ≤ sqDist (p i) (p j) := hsepi
      _ = (1 - 2 * r) ^ 2 * sqDist (q i) (q j) := hscale
      _ ≤ (1 - 2 * r) ^ 2 * (2 - Real.sqrt 3) := by
          apply mul_le_mul_of_nonneg_left hclose (sq_nonneg _)
      _ = ((1 - 2 * r) * (Real.sqrt (2 - Real.sqrt 3))) ^ 2 := by
          rw [mul_pow, hdsq]
  have hnn1 : (0 : ℝ) ≤ 2 * r := by linarith
  have hnn2 : (0 : ℝ) ≤ (1 - 2 * r) * (Real.sqrt (2 - Real.sqrt 3)) :=
    mul_nonneg (le_of_lt hs) (le_of_lt hd)
  have hlin : 2 * r ≤ (1 - 2 * r) * (Real.sqrt (2 - Real.sqrt 3)) := by
    have h1 : Real.sqrt ((2 * r) ^ 2) ≤ Real.sqrt (((1 - 2 * r) * (Real.sqrt (2 - Real.sqrt 3))) ^ 2) :=
      Real.sqrt_le_sqrt hkey
    rw [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at h1
    exact h1
  have h1d : (0 : ℝ) < 1 + Real.sqrt (2 - Real.sqrt 3) := by linarith
  have h2d : (0 : ℝ) < 2 * (1 + Real.sqrt (2 - Real.sqrt 3)) := by linarith
  rw [le_div_iff₀ h2d]
  linarith
