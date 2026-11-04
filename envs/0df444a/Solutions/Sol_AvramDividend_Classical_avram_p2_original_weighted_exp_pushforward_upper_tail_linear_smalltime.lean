-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_weighted_exp_pushforward_upper_tail_linear_smalltime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:13:05.975886+00:00
-- url     : https://prove2.me/submissions/f271f56f-6747-4420-89b5-369199b313db

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The first weighted exponential moment yields an original-space
positive-tail estimate, uniform in the mark threshold a. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ a : ℝ≥0∞,
          a * ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
              {z : ℝ | a ≤ ENNReal.ofReal z} ≤
          ENNReal.ofReal (C * h) := by
  obtain ⟨C, hC, hMoment⟩ :=
    avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound
      X 1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hMoment] with h hh a
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal z) :=
    ENNReal.measurable_ofReal
  have hle :
      (∫⁻ z : ℝ, ENNReal.ofReal z ∂
        ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))) ≤
      ENNReal.ofReal (C * h) := by
    simpa only [pow_one] using hh
  exact (mul_meas_ge_le_lintegral hf a).trans hle
