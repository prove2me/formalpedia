-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_upperfirst_terminal_ofReal_lintegral_eq_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:39:14.860998+00:00
-- url     : https://prove2.me/submissions/7fef4755-842b-42a9-a564-2ddbc8bb3e01

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_true_upperfirst_terminal_real_expectation
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_rewards_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- The original UBV strict upper-first q-scale payoff has the exact
extended-nonnegative expectation W(x), via genuine Bochner integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, ENNReal.ofReal
      (if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0) ∂P) = ENNReal.ofReal (W x) := by
  let F : Ω → ℝ := fun ω =>
    if twoSidedExitUpTime X (a-x) ω <
        twoSidedExitDownTime X (-x) ω then
      Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
    else 0
  have hInt : Integrable F P ∧ (∫ ω, F ω ∂P) = W x := by
    exact avram_root29_01_ubv_true_upperfirst_terminal_real_expectation
      X hnbv q hq W hW a x ha hx0 hxa
  have hNonneg (ω : Ω) : 0 ≤ F ω := by
    have h := (avram_ws01b_true_horizon_split_rewards_nonnegative
      X q W hW a x ha hx0 hxa
      (twoSidedExitUpTime X (a-x) ω).toNNReal ω).1
    simpa only [F, le_refl, and_true] using h
  change (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) = ENNReal.ofReal (W x)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt.1
    (Filter.Eventually.of_forall hNonneg), hInt.2]
