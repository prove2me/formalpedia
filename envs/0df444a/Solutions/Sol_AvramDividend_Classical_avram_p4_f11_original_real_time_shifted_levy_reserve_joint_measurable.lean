-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_original_real_time_shifted_levy_reserve_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:05:07.283828+00:00
-- url     : https://prove2.me/submissions/2e49afc6-1a5d-477c-b84d-a93a181ddb31

import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun p : ℝ × Ω =>
      1 + X.X (Real.toNNReal p.1) p.2) := by
  have hTime : Measurable
      (fun p : ℝ × Ω => Real.toNNReal p.1) :=
    measurable_real_toNNReal.comp measurable_fst
  have hPair : Measurable
      (fun p : ℝ × Ω => ((Real.toNNReal p.1, p.2) : ℝ≥0 × Ω)) :=
    Measurable.prod hTime measurable_snd
  have hX : Measurable
      (fun p : ℝ × Ω => X.X (Real.toNNReal p.1) p.2) :=
    (AvramDividend.Classical.chat04_levy_joint_time_state_measurable X).comp hPair
  exact measurable_const.add hX
