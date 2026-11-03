-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_discounted_grid_sampled_nonnegative_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:59:41.047193+00:00
-- url     : https://prove2.me/submissions/57172c24-bb8b-4fdb-b98f-cebf8eee3bdf

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_discounted_full_right_dividend_grid_sampled_nonnegative_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- The genuine initial Stieltjes atom and sampled-nonnegative grid right
dividends share a discounted stopped C1 cash and terminal-value budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C) (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      u 0 = 0 →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      (∀ n, 0 ≤ w (x + X.X (u n) ω - rightLimit D (u n) ω)) →
      ∀ n,
        rightLimit D 0 ω +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        w x +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by
  filter_upwards
    [avram_wave7_02_original_BV_discounted_full_right_dividend_grid_sampled_nonnegative_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad
      a b L ha hab hbC hL1 hLip q hq] with ω hGrid
  intro u hu hu0 hBand hSampleNonneg n
  have hBound := hGrid u hu hBand hSampleNonneg n
  have hInit :=
    (avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
      X x D hD w hjump ω).1
  have hStart : Real.exp (-(q * (u 0 : ℝ))) *
      w (x + X.X (u 0) ω - rightLimit D (u 0) ω) =
      w (x - rightLimit D 0 ω) := by
    rw [hu0, X.X_zero ω] <;> norm_num
  rw [hStart] at hBound
  linarith only [hBound, hInit]