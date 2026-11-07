-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_stopped_weighted_raw_jump_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:25:29.602904+00:00
-- url     : https://prove2.me/submissions/0950afb0-2898-43ab-a19d-a8b9f093b36b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original stopped BV path increment is dominated by its drift minus
    genuine negative-jump increments on one physical grid, with nonnegative
    (potentially state-dependent) weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) (hW : ∀ ω i, 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
      let s : ℕ → ℝ≥0 := fun i => min (u i) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (X.X (s (i + 1)) ω - X.X (s i) ω)) ≤
      ∑ i ∈ Finset.range (m + 1),
        W i ω *
          ((((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) -
            (J (s (i + 1)) - J (s i))) := by
  have hres :=
    AvramDividend.Classical.avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
      X hBV x D T m W hW
  filter_upwards [hres] with ω hω
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
  let s : ℕ → ℝ≥0 := fun i => min (u i) τ
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
  let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
  have hR :
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (R (s i) - R (s (i + 1)))) ≤ 0 := by
    simpa only [R, J, s, u, τ] using hω
  dsimp only
  have hcell (i : ℕ) :
      W i ω * (X.X (s (i + 1)) ω - X.X (s i) ω) =
        W i ω *
          ((((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) -
            (J (s (i + 1)) - J (s i))) +
        W i ω * (R (s i) - R (s (i + 1))) := by
    dsimp only [R]
    ring
  calc
    (∑ i ∈ Finset.range (m + 1),
      W i ω * (X.X (s (i + 1)) ω - X.X (s i) ω)) =
        ∑ i ∈ Finset.range (m + 1),
          (W i ω *
            ((((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) -
              (J (s (i + 1)) - J (s i))) +
           W i ω * (R (s i) - R (s (i + 1)))) := by
             apply Finset.sum_congr rfl
             intro i hi
             exact hcell i
    _ = (∑ i ∈ Finset.range (m + 1),
          W i ω *
            ((((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) -
              (J (s (i + 1)) - J (s i)))) +
        (∑ i ∈ Finset.range (m + 1),
          W i ω * (R (s i) - R (s (i + 1)))) := by
             rw [Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hR]
