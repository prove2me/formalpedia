-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_eq_of_finite_unit_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:46:37.467893+00:00
-- url     : https://prove2.me/submissions/d11d9e20-ad25-4777-9247-07c92a26a4f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_levy_image_borel_eq_candidate
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_unit_support_high_moment_mass_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_integrable_of_lintegral_ne_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The source-specific full Borel image uniqueness theorem needs only
finite unit-supported candidate laws and their genuine moment limits:
integrability and high-moment finiteness follow automatically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (η ρ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ] [η.Regular] [ρ.Regular]
    (hη : η = (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hunit_ρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
    (hmomρ : ∀ k, Tendsto (fun h : ℝ =>
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ))) :
    η = ρ := by
  have hunit_η : ∀ᵐ z ∂η, z ∈ Icc (0 : ℝ) 1 := by
    rw [hη]
    apply ae_iff.mpr
    exact avram_p2_negative_levy_weighted_exp_image_compact_support X
  have hfinite (μ : Measure ℝ) [IsFiniteMeasure μ]
      (hunit : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (k : ℕ) :
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤ := by
    have hb := avram_p2_i_moment_unit_support_high_moment_mass_bound μ hunit k
    exact ne_of_lt (lt_of_le_of_lt hb (measure_lt_top μ Set.univ))
  have hreal (μ : Measure ℝ) [IsFiniteMeasure μ]
      (hunit : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (k : ℕ) :
      Integrable (fun z : ℝ => z ^ k) μ := by
    have hpositive : ∀ᵐ z ∂μ, 0 ≤ z :=
      hunit.mono (fun z hz => hz.1)
    exact avram_p2_i_moment_integrable_of_lintegral_ne_top
      μ hpositive k (hfinite μ hunit k)
  exact avram_p2_m_uniqueness_original_levy_image_borel_eq_candidate
    X η ρ hη hne hunit_ρ
    (fun k => hreal η hunit_η k)
    (fun k => hreal ρ hunit_ρ k)
    (fun k => hfinite ρ hunit_ρ k) hmomρ
