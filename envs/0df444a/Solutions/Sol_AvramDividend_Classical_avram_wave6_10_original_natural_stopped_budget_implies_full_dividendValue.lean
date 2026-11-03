-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:53:32.55603+00:00
-- url     : https://prove2.me/submissions/11954caa-0dda-454b-9d24-e337e3d6b92c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_all_real_horizon_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform natural ruin-stopped payment budgets imply a full original
    dividend value budget, preserving all payment atoms including time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (A : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A) :
    dividendValue X q x D ≤ A := by
  apply dividendValue_le_of_uniform_truncated_bounds X q x D hD A
  intro n
  exact avram_wave6_10_original_natural_stopped_budget_implies_all_real_horizon_budget
    X q x D hD.1 A hBound (n : ℝ) (Nat.cast_nonneg n)
