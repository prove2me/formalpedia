-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_discounted_cap_grid_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:11:54.708754+00:00
-- url     : https://prove2.me/submissions/8215aa29-6d65-45a3-bf6b-a0146e7d26fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cap_overshoot_grid_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Discounting by a nonnegative rate does not increase the genuine
source cap-overshoot variation on any finite physical time grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) :
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
          Real.exp (-(q * (u i : ℝ))) *
            |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
              max (z i - c) 0|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) := by
  filter_upwards
    [avram_p3_bv_original_cap_overshoot_grid_envelope X hBV c]
    with ω hCap
  let J : ℝ≥0 → ℝ := fun t =>
    (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
    else 0)
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  change ∀ (n : ℕ) (u : ℕ → ℝ≥0) (z : ℕ → ℝ),
    (∀ i, i < n → u i ≤ u (i + 1)) →
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
          max (z i - c) 0|) ≤
      |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0))
  intro n u z hu
  calc
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
          max (z i - c) 0|) ≤
      (∑ i ∈ Finset.range n,
        |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
          max (z i - c) 0|) := by
            apply Finset.sum_le_sum
            intro i hi
            have hqi : 0 ≤ q * (u i : ℝ) :=
              mul_nonneg hq (u i).property
            have he : Real.exp (-(q * (u i : ℝ))) ≤ 1 :=
              Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqi)
            calc
              Real.exp (-(q * (u i : ℝ))) *
                  |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
                    max (z i - c) 0| ≤
                1 * |max (z i + (Y (u (i + 1)) - Y (u i)) - c) 0 -
                  max (z i - c) 0| :=
                    mul_le_mul_of_nonneg_right he (abs_nonneg _)
              _ = _ := one_mul _
    _ ≤ |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
      (R (u n) - R (u 0)) := hCap n u z hu
