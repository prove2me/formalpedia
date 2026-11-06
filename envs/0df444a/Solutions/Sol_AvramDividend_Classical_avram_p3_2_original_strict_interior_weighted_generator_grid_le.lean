-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_interior_weighted_generator_grid_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:51:48.082751+00:00
-- url     : https://prove2.me/submissions/6fb5d6d5-f339-4504-bdf9-c66d304a30c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_weighted_intrinsic_jump_drift_grid_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Discounted positive-gradient original-grid bound with the actual X/D rightpayment
reserve. Interior hypotheses are local to the finite grid, not global at cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (s t : Fin n → ℝ≥0)
      (hst : ∀ i, s i ≤ t i)
      (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
      (hInterior : ∀ i : Fin n,
        0 < x + X.X (s i) ω - rightLimit D (s i) ω ∧
        ENNReal.ofReal (x + X.X (s i) ω - rightLimit D (s i) ω) < C),
      (∑ i : Fin n,
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (x + X.X (s i) ω - rightLimit D (s i) ω)) *
        (X.X (t i) ω - X.X (s i) ω +
          (∫⁻ p, (if s i < p.1 ∧ p.1 ≤ t i then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ≤
      ∑ i : Fin n,
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (x + X.X (s i) ω - rightLimit D (s i) ω)) *
        (((t i : ℝ) - (s i : ℝ)) * X.drift) := by
  filter_upwards
    [avram_p3_2_original_weighted_intrinsic_jump_drift_grid_le
      X hBV] with ω hω
  intro n s t hst x D hInterior
  have hweights (i : Fin n) :
      0 ≤ Real.exp (-(q * (s i : ℝ))) *
        deriv w (x + X.X (s i) ω - rightLimit D (s i) ω) := by
    apply mul_nonneg (le_of_lt (Real.exp_pos _))
    have h := hw_grad _ (hInterior i).1 (hInterior i).2
    linarith
  exact hω n s t hst
    (fun i => Real.exp (-(q * (s i : ℝ))) *
      deriv w (x + X.X (s i) ω - rightLimit D (s i) ω)) hweights
