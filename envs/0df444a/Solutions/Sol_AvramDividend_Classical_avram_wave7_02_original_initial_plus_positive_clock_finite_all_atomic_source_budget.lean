-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_initial_plus_positive_clock_finite_all_atomic_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:04:55.507926+00:00
-- url     : https://prove2.me/submissions/80a22f28-4349-4112-a266-546f59d0fc28

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_source_and_dividend_finite_grid_discounted_jump_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- The full original time-zero right-payment atom and all selected positive
pre-ruin simultaneous source/payment jumps obey the exact discounted HJB
source-only upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (hTimes : ∀ t ∈ S, 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ t ∈ S,
        (Real.exp (-(q * (t : ℝ))) *
          ((w (x + X.X t ω - rightLimit D t ω) -
              w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
                D t ω)) +
            (rightLimit D t ω - D t ω)))) ≤
    w x + (∑ t ∈ S,
      (Real.exp (-(q * (t : ℝ))) *
        (w (x + X.X t ω - D t ω) -
          w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)))) := by
  have hZero :=
    (avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
      X x D hD w hjump ω).1
  have hPositive :=
    avram_wave7_02_original_positive_source_and_dividend_finite_grid_discounted_jump_budget
      X x q D w hjump ω S hTimes
  linarith only [hZero, hPositive]
