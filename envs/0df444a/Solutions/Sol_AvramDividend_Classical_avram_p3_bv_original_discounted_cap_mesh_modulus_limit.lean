-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_discounted_cap_mesh_modulus_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:26:28.200105+00:00
-- url     : https://prove2.me/submissions/f87d92db-97df-45c7-b9f9-1499afb15856

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_cap_grid_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Vanishing C1 moduli eliminate the discounted cap overshoot of the
genuine original jump-removed BV source over any stopped finite grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) (τ : ℝ≥0)
    (n : ℕ → ℕ) (u : ℕ → ℕ → ℝ≥0) (z : ℕ → ℕ → ℝ)
    (hGrid : ∀ k i, i < n k → u k i ≤ u k (i + 1))
    (hZero : ∀ k, u k 0 = 0)
    (hEnd : ∀ k, u k (n k) = τ)
    (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0)
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      Filter.Tendsto (fun k => ε k *
        ∑ i ∈ Finset.range (n k),
          Real.exp (-(q * (u k i : ℝ))) *
            |max (z k i + (Y (u k (i + 1)) - Y (u k i)) - c) 0 -
              max (z k i - c) 0|) Filter.atTop (nhds 0) := by
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
    ∑ i ∈ Finset.range (n k),
      Real.exp (-(q * (u k i : ℝ))) *
        |max (z k i + (Y (u k (i + 1)) - Y (u k i)) - c) 0 -
          max (z k i - c) 0|
  let B : ℝ := |X.drift| * (τ : ℝ) + (R τ - R 0)
  change Filter.Tendsto (fun k => ε k * A k) Filter.atTop (nhds 0)
  have hA0 (k : ℕ) : 0 ≤ A k := by
    dsimp only [A]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hAB (k : ℕ) : A k ≤ B := by
    have hb := hCap (n k) (u k) (z k) (hGrid k)
    simpa only [A, B, J, R, Y, hZero k, hEnd k,
      NNReal.coe_zero, sub_zero] using hb
  have hupper (k : ℕ) : ε k * A k ≤ ε k * B :=
    mul_le_mul_of_nonneg_left (hAB k) (hε0 k)
  have hbound : Filter.Tendsto (fun k => ε k * B)
      Filter.atTop (nhds 0) := by
    simpa using hεlim.mul_const B
  exact squeeze_zero (fun k => mul_nonneg (hε0 k) (hA0 k))
    hupper hbound
