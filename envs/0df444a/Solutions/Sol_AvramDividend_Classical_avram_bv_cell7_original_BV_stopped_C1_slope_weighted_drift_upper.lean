-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_C1_slope_weighted_drift_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:23:45.116149+00:00
-- url     : https://prove2.me/submissions/c6b9272a-3fd0-40a4-af12-0e09ada97760

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual original stopped BV source has a drift upper bound even when
    each physical cell is weighted by its own nonnegative C1 value slope.
    The source uses the exact raw negative-jump tsum and its nonincreasing
    residual, without assuming that this residual vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let z : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      (∀ i ∈ Finset.range (m + 1), 0 ≤ deriv w (z i)) →
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
          (Y (u (i + 1)) - Y (u i))) ≤
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) := by
  have hR :=
    AvramDividend.Classical.avram_bv_residual10_original_raw_R_ae_monotone
      X hBV
  filter_upwards [hR] with ω hω
  intro m
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  let z : ℕ → ℝ := fun i =>
    x + X.X (u i) ω - rightLimit D (u i) ω
  change (∀ i ∈ Finset.range (m + 1), 0 ≤ deriv w (z i)) →
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
        (Y (u (i + 1)) - Y (u i))) ≤
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))
  intro hz
  have hu : Monotone u :=
    AvramDividend.Classical.avram_p3_2_physical_stopped_grid_monotone T τ m
  apply Finset.sum_le_sum
  intro i hi
  have hmono := hω (hu (Nat.le_succ i))
  have hcell : Y (u (i + 1)) - Y (u i) ≤
      ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift := by
    dsimp [Y, J]
    dsimp at hmono
    linarith
  exact mul_le_mul_of_nonneg_left hcell
    (mul_nonneg (le_of_lt (Real.exp_pos _)) (hz i hi))
