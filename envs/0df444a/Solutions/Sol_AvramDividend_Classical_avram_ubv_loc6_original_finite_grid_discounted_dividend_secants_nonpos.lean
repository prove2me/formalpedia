-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_finite_grid_discounted_dividend_secants_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:29:23.28847+00:00
-- url     : https://prove2.me/submissions/d91fc04e-3d8d-4bab-807c-93be2948c6cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On any genuine finite pre-ruin grid, all discounted dividend secant
    residuals have the required HJB sign, including the time-zero atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (hS : ∀ t ∈ S, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ S, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))))) ≤ 0 := by
  classical
  apply Finset.sum_nonpos
  intro t ht
  have hsec : (rightLimit D t ω - D t ω) -
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) ≤ 0 :=
    sub_nonpos.mpr (hjump ω t (hS t ht))
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hsec
