-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_moments_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:37:39.916205+00:00
-- url     : https://prove2.me/submissions/b335c3b2-dca9-4ca8-bb6b-8addd0b1e2ef

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_exp_image_ofReal_pow_lintegrals_eq

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual positive-time rescaled original weighted exponential image
has polynomial moments converging to the original negative Lévy image.
The zero extension makes the approximate measure defined on all real times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    Tendsto
      (fun h : ℝ => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then
          (ENNReal.ofReal h)⁻¹ •
            ((P.withDensity (fun ω => ENNReal.ofReal
              ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
              (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
        else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
          Real.exp))) := by
  let μh (h : ℝ) : Measure ℝ :=
    ((P.withDensity (fun ω => ENNReal.ofReal
      ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
      (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
  let η : Measure ℝ :=
    ((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4)))
  have hImg (h : ℝ) :
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μh h) =
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μh h) := by
    have hY : Measurable (X.X (Real.toNNReal h)) :=
      (X.adapted (Real.toNNReal h)).mono
        (𝓕.le (Real.toNNReal h)) le_rfl
    exact avram_p2_k_exp_image_ofReal_pow_lintegrals_eq
      (P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4)))
      (X.X (Real.toNNReal h)) hY k
  have hLim :
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η.map Real.exp) =
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂η.map Real.exp) :=
    avram_p2_k_exp_image_ofReal_pow_lintegrals_eq η id measurable_id k
  have heq :
      (fun h : ℝ => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ • μh h
         else (0 : Measure ℝ))) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun h : ℝ => (ENNReal.ofReal h)⁻¹ *
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μh h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    rw [if_pos hpos]
    rw [lintegral_smul_measure, smul_eq_mul, hImg h]
  change Tendsto
    (fun h : ℝ => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      (if 0 < h then (ENNReal.ofReal h)⁻¹ • μh h
       else (0 : Measure ℝ)))
    (nhdsWithin (0 : ℝ) (Ioi 0))
    (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η.map Real.exp))
  rw [hLim]
  exact (avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
    X k).congr' heq.symm
