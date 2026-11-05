-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_cap_overshoot_grid_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:04:17.308198+00:00
-- url     : https://prove2.me/submissions/bea31073-2fc5-49dc-afd4-d5ec050c8507

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_overshoot_step_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Every finite-grid cap overshoot in the genuine original jump-removed
source is dominated by its physical drift plus monotone BV residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (c : ℝ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0) (z : ℕ → ℝ),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
            max (z i - c) 0|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) := by
  filter_upwards
    [avram_p3_main_original_jump_removed_grid_variation X hBV]
    with ω hVar
  dsimp only
  let J : ℝ≥0 → ℝ := fun t =>
    (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
    else 0)
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  intro n u z hGrid
  calc
    (∑ i ∈ Finset.range n,
      |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
        max (z i - c) 0|) ≤
        (∑ i ∈ Finset.range n, |Y (u (i + 1)) - Y (u i)|) := by
          apply Finset.sum_le_sum
          intro i hi
          exact avram_p3_bv_finite_cap_overshoot_step_lipschitz
            c (z i) (Y (u (i + 1)) - Y (u i))
    _ ≤ |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0)) := hVar n u hGrid
