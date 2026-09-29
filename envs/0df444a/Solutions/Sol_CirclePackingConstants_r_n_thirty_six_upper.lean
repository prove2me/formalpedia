-- Prove2me | solution 1 for CirclePackingConstants.r_n_thirty_six_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T07:05:46.591967+00:00
-- url     : https://prove2.me/submissions/f935117c-0d17-4202-bed5-ccf7843afbfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_thirty_six_unit_square_close_pair

open CirclePackingConstants

/-- Reduction of the 36-circle radius upper bound to the sharp unit-square
close-pair statement d₃₆ ≤ 1/5. -/
theorem solution : r_n 36 ≤ (1 : ℝ) / 12 := by
  have hpack0 : Packable 36 0 := by
    refine ⟨le_rfl, by norm_num, (fun _ => (0, 0)), ?_, ?_⟩
    · intro i
      exact ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩
    · intro i j _
      unfold sqDist
      norm_num

  show sSup {r : ℝ | Packable 36 r} ≤ _
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
    have h01 : (0 : Fin 36) ≠ 1 := by decide
    have hbad := hsep 0 1 h01
    rw [hall 0, hall 1] at hbad
    simp only [sqDist] at hbad
    norm_num at hbad

  have hs : (0 : ℝ) < 1 - 2 * r := by
    have hrlt : r < 1 / 2 := lt_of_le_of_ne hr1 hne
    linarith
  have hsne : (1 : ℝ) - 2 * r ≠ 0 := ne_of_gt hs

  set q : Fin 36 → Point :=
    fun i => (((p i).1 - r) / (1 - 2 * r), ((p i).2 - r) / (1 - 2 * r)) with hq

  have hqmem :
      ∀ i, 0 ≤ (q i).1 ∧ (q i).1 ≤ 1 ∧ 0 ≤ (q i).2 ∧ (q i).2 ≤ 1 := by
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
    CirclePackingConstants.thirty_six_unit_square_close_pair q hqmem
  have hsepi := hsep i j hij

  have hscale :
      sqDist (p i) (p j) = (1 - 2 * r) ^ 2 * sqDist (q i) (q j) := by
    simp only [sqDist, hq]
    field_simp
    ring

  have hkey : (2 * r) ^ 2 ≤ ((1 - 2 * r) * ((1 : ℝ) / 5)) ^ 2 := by
    calc
      (2 * r) ^ 2 ≤ sqDist (p i) (p j) := hsepi
      _ = (1 - 2 * r) ^ 2 * sqDist (q i) (q j) := hscale
      _ ≤ (1 - 2 * r) ^ 2 * ((1 : ℝ) / 25) := by
          apply mul_le_mul_of_nonneg_left hclose (sq_nonneg _)
      _ = ((1 - 2 * r) * ((1 : ℝ) / 5)) ^ 2 := by ring

  have hnn1 : (0 : ℝ) ≤ 2 * r := by linarith
  have hnn2 : (0 : ℝ) ≤ (1 - 2 * r) * ((1 : ℝ) / 5) :=
    mul_nonneg (le_of_lt hs) (by norm_num)

  have hlin : 2 * r ≤ (1 - 2 * r) * ((1 : ℝ) / 5) := by
    have hsqrt :
        Real.sqrt ((2 * r) ^ 2) ≤
          Real.sqrt (((1 - 2 * r) * ((1 : ℝ) / 5)) ^ 2) :=
      Real.sqrt_le_sqrt hkey
    rw [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at hsqrt
    exact hsqrt

  linarith

#print axioms solution
