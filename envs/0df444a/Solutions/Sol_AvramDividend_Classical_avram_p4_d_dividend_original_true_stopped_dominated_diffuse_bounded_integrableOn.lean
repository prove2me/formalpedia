-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_dominated_diffuse_bounded_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:34:17.202028+00:00
-- url     : https://prove2.me/submissions/39180c3a-48e3-4fde-81a5-3f87ac43ba53

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An arbitrary path-selected submeasure of the original dividend Stieltjes
measure is finite on every true stopped payment set, so bounded measurable
signed kernels are integrable against its diffuse part. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f
      (ν.restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (K : ℝ)
    (hK : ∀ᵐ u ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      ‖f u‖ ≤ K) :
    IntegrableOn f (paymentTimes σ ∩ Iic (T : ℝ)) ν := by
  let S : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hsubset : S ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active σ u hu.1).1, hu.2⟩
  have hmass : ν S < ⊤ := by
    calc
      ν S ≤ (dividendMeasure D ω) S := hdom S
      _ ≤ (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) :=
        measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact IntegrableOn.of_bound hmass hf K hK
