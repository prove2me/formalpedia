-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_raw_cell_eq_cumulative_J_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:07:26.667128+00:00
-- url     : https://prove2.me/submissions/d61e0c28-ad1c-485a-b716-e3ba5432b2c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every original raw jump sum in a physical source cell equals
the corresponding genuine cumulative-J increment, simultaneously for
all stopped monotone finite grids on one full-measure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      (∀ i : ℕ, i < n → u i ≤ u (i + 1)) →
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      ∀ i : ℕ, i < n →
        (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = J (u (i + 1)) - J (u i) := by
  have hAdd :=
    avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
      X hBV
  filter_upwards [hAdd] with ω hω
  intro u n hu J i hi
  have hCell := hω (u i) (u (i + 1)) (hu i hi)
  dsimp only [J]
  linarith [hCell]
