-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_sum_le_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:45:02.761677+00:00
-- url     : https://prove2.me/submissions/624c2d13-0cef-4732-ad5a-f4b4aebd738a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_one_grid_cell_pair_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_disjoint_grid_pair_card_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual source finite-grid marked-count sum is bounded by all chronological pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ)
    (hst : ∀ i, s i ≤ t i) (htT : ∀ i, t i ≤ T)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (∑ i : Fin m, N 0 (s i) * N (s i) (t i)) ≤
      (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ≥0∞) := by
  classical
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let C : Fin m → Finset (ℝ≥0 × ℝ≥0) := fun i =>
    (F ×ˢ F).filter (fun p => p.1 ≤ s i ∧ s i < p.2 ∧ p.2 ≤ t i)
  let K : Finset (ℝ≥0 × ℝ≥0) :=
    (F ×ˢ F).filter (fun p => p.1 < p.2)
  change (∑ i : Fin m, N 0 (s i) * N (s i) (t i)) ≤ (K.card : ℝ≥0∞)
  have hpoint (i : Fin m) : N 0 (s i) * N (s i) (t i) =
      (C i).card := by
    simpa only [N, B, F, C] using
      (avram_p2_e_compensator_original_one_grid_cell_pair_count
        X ω T (s i) (t i) (hst i) (htT i) n)
  have hBound : (∑ i : Fin m, (C i).card) ≤ K.card := by
    simpa only [F, C, K] using
      (avram_p2_e_compensator_original_disjoint_grid_pair_card_le
        X ω T m s t n hdisj)
  calc
    (∑ i : Fin m, N 0 (s i) * N (s i) (t i)) =
        ∑ i : Fin m, ((C i).card : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hpoint i
    _ ≤ (K.card : ℝ≥0∞) := by exact_mod_cast hBound
