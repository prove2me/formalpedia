-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger20_original_top_virtualcap_source_mesh_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:31:39.095329+00:00
-- url     : https://prove2.me/submissions/3d538c2f-cd94-4689-b44f-6674ae55d89d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_gradient_growth_to_cap
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_discounted_cap_gaussian_mesh_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A deterministic virtual ceiling controls the original Gaussian frozen-source
    mesh above a compact stopping band, even when the real cap is infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (u b L : ℝ) (hub : u < b) (hL : 0 ≤ L)
    (hwcont : ContinuousOn w (Icc u b))
    (hwderiv : ∀ y ∈ Ioo u b, HasDerivAt w (deriv w y) y)
    (hgrad : ∀ y ∈ Ico u b, 1 ≤ deriv w y)
    (hquad : ∀ y ∈ Ico u b, ∀ z ∈ Icc u b,
      w z ≤ w y + deriv w y * (z - y) + L / 2 * (z - y) ^ 2)
    (q : ℝ) (ω : Ω) (S : Finset ℕ)
    (s t : ℕ → ℝ≥0)
    (hfloor : ∀ i ∈ S,
      u ≤ x + X.X (s i) ω - rightLimit D (s i) ω ∧
      u ≤ x + X.X (t i) ω - rightLimit D (s i) ω) :
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let g : ℝ → ℝ := fun y => if y < b then deriv w y else 1
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (t i) ω - rightLimit D (s i) ω
    (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) *
      (V (Z i) - V (Y i) - g (Y i) * (Z i - Y i))) ≤
      L / 2 * (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) * (Z i - Y i) ^ 2) := by
  have hgrowth : ∀ z ∈ Icc u b, b - z ≤ w b - w z := by
    apply avram_gauss_finitec2_gradient_growth_to_cap
      w u b hub hwcont hwderiv
    intro y hy
    exact hgrad y ⟨hy.1.le, hy.2⟩
  exact avram_gfinite15_original_discounted_cap_gaussian_mesh_bound
    X x D w u b L hub hL hgrad hquad hgrowth q ω S s t hfloor
