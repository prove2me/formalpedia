-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_borel_eq_candidate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:27:34.797185+00:00
-- url     : https://prove2.me/submissions/187cc552-b8d8-49ad-b832-def67281fbb0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_moments_converge
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A finite regular candidate with the genuine original Levy weighted
small-time image moments equals the actual negative Levy image measure
on all Borel sets, including endpoint atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (η ρ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ] [η.Regular] [ρ.Regular]
    (hη : η = (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hunit_ρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
    (hrealη : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) η)
    (hrealρ : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) ρ)
    (hfiniteρ : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ) ≠ ⊤)
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
  letI : (nhdsWithin (0 : ℝ) (Ioi 0)).NeBot := hne
  have hunitη : ∀ᵐ z ∂η, z ∈ Icc (0 : ℝ) 1 := by
    rw [hη]
    apply ae_iff.mpr
    exact avram_p2_negative_levy_weighted_exp_image_compact_support X
  have hmomη : ∀ k, Tendsto (fun h : ℝ =>
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η)) := by
    intro k
    rw [hη]
    exact avram_p2_k_original_normalized_weighted_image_moments_converge X k
  have heq : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ) := by
    intro k
    exact tendsto_nhds_unique (hmomη k) (hmomρ k)
  exact avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
    η ρ hunitη hunit_ρ hrealη hrealρ hfiniteρ heq
