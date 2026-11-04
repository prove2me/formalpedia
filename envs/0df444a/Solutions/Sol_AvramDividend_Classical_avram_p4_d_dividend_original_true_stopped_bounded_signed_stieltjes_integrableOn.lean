-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:35:45.542464+00:00
-- url     : https://prove2.me/submissions/246b5571-259d-4496-881c-e35abf9eec2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every bounded measurable signed kernel is Stieltjes-integrable on actual stopped payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f
      ((dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (C : ℝ)
    (hC : ∀ᵐ u ∂(dividendMeasure D ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      ‖f u‖ ≤ C) :
    IntegrableOn f (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let s : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hsubset : s ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active σ u hu.1).1, hu.2⟩
  have hmass : μ s < ⊤ := by
    calc
      μ s ≤ μ (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact IntegrableOn.of_bound hmass hf C hC
