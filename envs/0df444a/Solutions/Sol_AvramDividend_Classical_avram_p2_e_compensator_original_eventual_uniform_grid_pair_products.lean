-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_eventual_uniform_grid_pair_products
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:59:21.728076+00:00
-- url     : https://prove2.me/submissions/85567e8d-552a-4392-b10b-220b20e902f1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_eventual_uniform_grid_pair_card
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_uniform_grid_pair_sum_card
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The source pathwise uniform pair products eventually equal its genuine chronological pair cardinal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ᶠ k : ℕ in Filter.atTop,
      (let s : Fin (k + 1) → ℝ≥0 := fun i =>
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
       ∑ i : Fin (k + 1), N 0 (s i) * N (s i) (t i)) =
        (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ≥0∞) := by
  classical
  dsimp only
  have hEvent :=
    avram_p2_e_compensator_original_eventual_uniform_grid_pair_card
      X ω T hT n
  filter_upwards [hEvent] with k hk
  have hExact :=
    avram_p2_e_compensator_original_uniform_grid_pair_sum_card
      X ω T k n
  exact hExact.trans (congrArg (fun z : ℕ => (z : ℝ≥0∞)) hk.symm)
