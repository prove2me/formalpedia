-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite15_original_discounted_cap_gaussian_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:18:18.039886+00:00
-- url     : https://prove2.me/submissions/35ba596a-a809-4b97-9c00-5bc7bb73e647

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_cap_quadratic_glue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (u c L : ℝ) (huC : u < c) (hL : 0 ≤ L)
    (hgrad : ∀ z ∈ Ico u c, 1 ≤ deriv w z)
    (hquad : ∀ z ∈ Ico u c, ∀ y ∈ Icc u c,
      w y ≤ w z + deriv w z * (y - z) + L / 2 * (y - z) ^ 2)
    (hgrowth : ∀ y ∈ Icc u c, c - y ≤ w c - w y)
    (q : ℝ) (ω : Ω) (S : Finset ℕ)
    (s t : ℕ → ℝ≥0)
    (hfloor : ∀ i ∈ S,
      u ≤ x + X.X (s i) ω - rightLimit D (s i) ω ∧
      u ≤ x + X.X (t i) ω - rightLimit D (s i) ω) :
    let V : ℝ → ℝ := fun y =>
      if y ≤ c then w y else w c + (y - c)
    let g : ℝ → ℝ := fun y => if y < c then deriv w y else 1
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (t i) ω - rightLimit D (s i) ω
    (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) *
      (V (Z i) - V (Y i) - g (Y i) * (Z i - Y i))) ≤
      L / 2 * (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) * (Z i - Y i) ^ 2) := by
  dsimp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hrow := hfloor i hi
  have hcap := avram_gauss_finitec2_cap_quadratic_glue
    w u c L huC hL hgrad hquad hgrowth
    (x + X.X (s i) ω - rightLimit D (s i) ω)
    (x + X.X (t i) ω - rightLimit D (s i) ω)
    hrow.1 hrow.2
  have hquadrow :
      (if x + X.X (t i) ω - rightLimit D (s i) ω ≤ c then
          w (x + X.X (t i) ω - rightLimit D (s i) ω)
        else w c + (x + X.X (t i) ω - rightLimit D (s i) ω - c)) -
      (if x + X.X (s i) ω - rightLimit D (s i) ω ≤ c then
          w (x + X.X (s i) ω - rightLimit D (s i) ω)
        else w c + (x + X.X (s i) ω - rightLimit D (s i) ω - c)) -
      (if x + X.X (s i) ω - rightLimit D (s i) ω < c then
          deriv w (x + X.X (s i) ω - rightLimit D (s i) ω)
        else 1) *
        ((x + X.X (t i) ω - rightLimit D (s i) ω) -
         (x + X.X (s i) ω - rightLimit D (s i) ω)) ≤
      L / 2 *
        ((x + X.X (t i) ω - rightLimit D (s i) ω) -
         (x + X.X (s i) ω - rightLimit D (s i) ω)) ^ 2 := by
    dsimp at hcap
    linarith
  have he : 0 ≤ Real.exp (-(q * (t i : ℝ))) :=
    (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hquadrow he
  nlinarith [hmul]
