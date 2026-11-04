-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_unit_support_high_moment_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:28:51.141925+00:00
-- url     : https://prove2.me/submissions/6c68cafc-9b69-4831-9ede-7d04e6d4cb41

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ)
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≤ μ Set.univ := by
  have hbound : ∀ᵐ z ∂μ, (ENNReal.ofReal z) ^ k ≤ 1 := by
    filter_upwards [hμ] with z hz
    have hle : ENNReal.ofReal z ≤ ENNReal.ofReal (1 : ℝ) :=
      ENNReal.ofReal_le_ofReal hz.2
    simpa using (ENNReal.pow_le_pow_left hle :
      (ENNReal.ofReal z) ^ k ≤ (ENNReal.ofReal (1 : ℝ)) ^ k)
  calc
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≤
        ∫⁻ z : ℝ, (1 : ℝ≥0∞) ∂μ := lintegral_mono_ae hbound
    _ = μ Set.univ := by simp
