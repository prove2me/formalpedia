-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_uniform_grid_pair_sum_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:23:36.253128+00:00
-- url     : https://prove2.me/submissions/b7ae63f7-cc4f-45c2-b605-2a57241e488f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_one_grid_cell_pair_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_cell_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (k n : ℕ) :
    let s : Fin (k + 1) → ℝ≥0 := fun i =>
      (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1))
    let t : Fin (k + 1) → ℝ≥0 := fun i =>
      (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)))
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
    (∑ i : Fin (k + 1), N 0 (s i) * N (s i) (t i)) =
      ((∑ i : Fin (k + 1),
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
          p.1 ≤ s i ∧ s i < p.2 ∧ p.2 ≤ t i)).card : ℕ) : ℝ≥0∞) := by
  dsimp only
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have h := avram_p2_e_compensator_uniform_grid_cell_bounds T k i
  exact avram_p2_e_compensator_original_one_grid_cell_pair_count
    X ω T
    ((i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1)))
    (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)))
    h.1 h.2 n
