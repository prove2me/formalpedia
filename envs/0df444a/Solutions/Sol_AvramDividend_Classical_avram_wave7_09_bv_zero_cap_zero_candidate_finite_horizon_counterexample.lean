-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:07:14.837993+00:00
-- url     : https://prove2.me/submissions/99567cde-8a17-4bc3-84c0-134c8fab021d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Conditional actual-source certificate: genuine C=0 admissibility,
a nonnegative finite horizon and strict failure of the zero-value bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    IsAdmissibleLe X 0 0 (barrierStrategy X 0 0) ∧
    ∃ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ∧
      ¬ ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
          ENNReal.ofReal ((fun _ : ℝ => (0 : ℝ)) (0 : ℝ))) := by
  constructor
  · simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
  · obtain ⟨n, hn⟩ :=
      avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
        X hX hBV hFinite q hq
    refine ⟨n, by positivity, ?_⟩
    simpa only [ENNReal.ofReal_zero] using (not_le_of_gt hn)
