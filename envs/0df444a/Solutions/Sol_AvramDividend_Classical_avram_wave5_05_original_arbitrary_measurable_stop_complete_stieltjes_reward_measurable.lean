-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:20:50.8129+00:00
-- url     : https://prove2.me/submissions/af9d137f-0fbd-46d4-a25a-78b3496a8d60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (S : Ω → ℝ≥0∞) (hSm : Measurable S) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by
  classical
  let τ : Ω → ℝ≥0∞ := fun ω => min (ruinTime X x D ω) (S ω)
  have hRuinM : Measurable (ruinTime X x D) :=
    (ruinTime_stopping_rightCont_filtration X x D hD).measurable'
  have hτ : Measurable τ := hRuinM.min hSm
  let E : Ω → Set ℝ := fun ω => paymentTimes (τ ω) ∩ Iic T
  have hE (ω : Ω) : MeasurableSet (E ω) :=
    (paymentTimes_measurable (τ ω)).inter measurableSet_Iic
  let A : Set (ℝ × Ω) :=
    {p | p.1 ∈ paymentTimes (τ p.2) ∧ p.1 ≤ T}
  have hA : MeasurableSet A :=
    (paymentTimes_joint_measurable τ hτ).inter
      (measurableSet_le measurable_fst measurable_const)
  let W : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hW : Measurable W :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_id).neg))
  obtain ⟨κ, hκs, hκ⟩ :=
    dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκs
  have hKernel := measurable_random_indicator_lintegral κ A hA W hW
  have hEq : (fun ω : Ω => ∫⁻ t in E ω, W t ∂dividendMeasure D ω) =
      (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ A then W t else 0 ∂κ ω) := by
    funext ω
    rw [hκ ω, ← lintegral_indicator (hE ω) W]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ E ω
    · have htA : (t, ω) ∈ A := ht
      simp [Set.indicator, ht, htA]
    · have htA : (t, ω) ∉ A := fun hs => ht hs
      simp [Set.indicator, ht, htA]
  change Measurable (fun ω : Ω => ∫⁻ t in E ω, W t ∂dividendMeasure D ω)
  rw [hEq]
  simpa only [A, Set.mem_setOf_eq] using hKernel
