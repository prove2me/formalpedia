-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_centred_clipped_futureIncrement_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:41:48.962994+00:00
-- url     : https://prove2.me/submissions/552f423d-6b1e-477d-9e3c-2841fd2b89fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_general_future_increment_conditional_expectation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exactly centred bounded truncation of every original Lévy
future increment has zero past-conditional expectation, with no first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (K : ℝ) (hK : 0 ≤ K) :
    P[(fun ω =>
      max (-K) (min K (X.X t ω - X.X s ω)) -
        ∫ η, max (-K) (min K (X.X (t - s) η)) ∂P) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let clip : ℝ → ℝ := fun y => max (-K) (min K y)
  have hclip : Measurable clip := by
    fun_prop
  have hbound : ∀ y, ‖clip y‖ ≤ K := by
    intro y
    have hlo : -K ≤ clip y := le_max_left _ _
    have hup : clip y ≤ K :=
      max_le (by linarith) (min_le_left _ _)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hup⟩
  have hInt := avram_wave3_04_source_bounded_futurePayoff_integrable
    X (t - s) clip hclip K hbound
  let mean : ℝ := ∫ η, clip (X.X (t - s) η) ∂P
  have hψ : Measurable (fun y => clip y - mean) :=
    hclip.sub measurable_const
  have hIntψ : Integrable
      (fun ω => clip (X.X (t - s) ω) - mean) P :=
    hInt.sub (integrable_const mean)
  have hMeanZero :
      (∫ ω, clip (X.X (t - s) ω) - mean ∂P) = 0 := by
    rw [integral_sub hInt (integrable_const mean)]
    simp [mean]
  have hConditional :=
    chat04_general_future_increment_conditional_expectation
      X s t hst (fun y => clip y - mean) hψ hIntψ
  simpa only [clip, mean, hMeanZero] using hConditional
