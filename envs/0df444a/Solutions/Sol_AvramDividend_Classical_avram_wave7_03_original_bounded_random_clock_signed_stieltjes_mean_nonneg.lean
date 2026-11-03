-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_signed_stieltjes_mean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:35:31.221643+00:00
-- url     : https://prove2.me/submissions/6cac1d21-dd1f-44d0-80ef-0e060606e68c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The genuine expected real Stieltjes reward on the original random
    stopped dividend measure is nonnegative, including all payout types. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    0 ≤ (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  apply integral_nonneg
  intro ω
  apply integral_nonneg
  intro t
  exact (Real.exp_pos (-(q * t))).le
