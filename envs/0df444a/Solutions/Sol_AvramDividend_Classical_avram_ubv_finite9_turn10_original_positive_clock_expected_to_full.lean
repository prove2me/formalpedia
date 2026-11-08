-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn10_original_positive_clock_expected_to_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:31:58.00326+00:00
-- url     : https://prove2.me/submissions/fe71a226-5ab5-489e-ad19-1195cbd549dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_clock_partition_mean_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict positive-clock expected estimates yield the complete original
discounted Lévy reward budget.  The zero-clock step retains the original
right-payment cash atom and the dividend jump inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hpositive : ∀ k,
      (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
        w x * (P {ω : Ω | σ k ω ≠ 0}).toReal) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  exact avram_ubv_finite9_turn10_clock_partition_mean_upper
    (w x) (σ k) (F k)
    (avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k))
    (hFI k)
    (fun ω hz =>
      avram_ubv_loc6_original_zero_clock_exact_physical_F_le
        X x q w C D hD hjump σ F hFsource k ω hz)
    (hpositive k)
