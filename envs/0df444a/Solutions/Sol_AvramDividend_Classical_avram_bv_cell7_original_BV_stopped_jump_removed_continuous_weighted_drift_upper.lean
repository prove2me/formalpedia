-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_jump_removed_continuous_weighted_drift_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:38:03.881035+00:00
-- url     : https://prove2.me/submissions/eb6e099e-33cf-402a-9f86-c2a410ade20e

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

/-- On the actual original stopped physical grid, the jump-removed BV source
    increments have a nonpositive residual against the physical Levy drift.
    The real negative-jump tsum is retained exactly, with no residual-zero
    or equality-in-law assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (T : ℝ≥0) (m : ℕ) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      (∑ i ∈ Finset.range (m + 1),
        Real.exp (-(q * (u i : ℝ))) * (Y (u (i + 1)) - Y (u i))) ≤
      (∑ i ∈ Finset.range (m + 1),
        Real.exp (-(q * (u i : ℝ))) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) := by
  have hR :=
    AvramDividend.Classical.avram_bv_residual10_original_raw_R_ae_monotone
      X hBV
  filter_upwards [hR] with ω hω
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  change (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u i : ℝ))) * (Y (u (i + 1)) - Y (u i))) ≤
    (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u i : ℝ))) *
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))
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
  exact mul_le_mul_of_nonneg_left hcell (le_of_lt (Real.exp_pos _))
