-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_random_clock_cap_mesh_modulus_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:28:19.38656+00:00
-- url     : https://prove2.me/submissions/82141116-8b44-4937-8fa7-a17a7b02cbdc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_cap_grid_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- At the genuine original random clock, every discounted physical cap
overshoot with a vanishing C1 modulus disappears pathwise almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) (τ : Ω → ℝ≥0)
    (n : Ω → ℕ → ℕ) (u : Ω → ℕ → ℕ → ℝ≥0)
    (z : Ω → ℕ → ℕ → ℝ)
    (hGrid : ∀ ω k i, i < n ω k → u ω k i ≤ u ω k (i + 1))
    (hZero : ∀ ω k, u ω k 0 = 0)
    (hEnd : ∀ ω k, u ω k (n ω k) = τ ω)
    (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0)
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      Filter.Tendsto (fun k => ε k *
        ∑ i ∈ Finset.range (n ω k),
          Real.exp (-(q * (u ω k i : ℝ))) *
            |max (z ω k i + (Y (u ω k (i + 1)) - Y (u ω k i)) - c) 0 -
              max (z ω k i - c) 0|) Filter.atTop (nhds 0) := by
  filter_upwards
    [avram_p3_bv_original_discounted_cap_grid_envelope X hBV q hq c]
    with ω hCap
  let J : ℝ≥0 → ℝ := fun t =>
    (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
    else 0)
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  let A : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.range (n ω k),
      Real.exp (-(q * (u ω k i : ℝ))) *
        |max (z ω k i + (Y (u ω k (i + 1)) - Y (u ω k i)) - c) 0 -
          max (z ω k i - c) 0|
  let B : ℝ := |X.drift| * (τ ω : ℝ) + (R (τ ω) - R 0)
  change Filter.Tendsto (fun k => ε k * A k) Filter.atTop (nhds 0)
  have hA0 (k : ℕ) : 0 ≤ A k := by
    dsimp only [A]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hAB (k : ℕ) : A k ≤ B := by
    have hb := hCap (n ω k) (u ω k) (z ω k) (hGrid ω k)
    simpa only [A, B, J, R, Y, hZero ω k, hEnd ω k,
      NNReal.coe_zero, sub_zero] using hb
  have hupper (k : ℕ) : ε k * A k ≤ ε k * B :=
    mul_le_mul_of_nonneg_left (hAB k) (hε0 k)
  have hbound : Filter.Tendsto (fun k => ε k * B)
      Filter.atTop (nhds 0) := by
    simpa using hεlim.mul_const B
  exact squeeze_zero (fun k => mul_nonneg (hε0 k) (hA0 k))
    hupper hbound
