-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_cap_large_mark_drift_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:24:16.339195+00:00
-- url     : https://prove2.me/submissions/94b70393-37c9-4421-aad1-28717c1a97e2

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_raw_uniform_on_prejump_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite source ν intensity uniformly bounds the original large raw
jump drift across the entire capped reserve interval, including zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc 0 v,
      |∫ z in Iio (-ε), w (y + z) - w y ∂X.ν| ≤ B := by
  obtain ⟨M, hMnonneg, hM⟩ :=
    avram_p4_c_generator_large_raw_uniform_on_prejump_cap
      w v hv hw_cont hw_neg
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  refine ⟨M * X.ν.real (Iio (-ε)),
    mul_nonneg hMnonneg measureReal_nonneg, ?_⟩
  intro y hy
  have hbound (z : ℝ) (hz : z ∈ Iio (-ε)) :
      ‖w (y + z) - w y‖ ≤ M := by
    have hzneg : z < 0 := by
      change z < -ε at hz
      linarith
    simpa only [Real.norm_eq_abs] using hM y hy z hzneg
  have h := norm_setIntegral_le_of_norm_le_const htail hbound
  simpa only [Real.norm_eq_abs] using h
