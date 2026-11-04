-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_real_moments_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:57:16.857849+00:00
-- url     : https://prove2.me/submissions/46293c2a-26ea-4fa9-bb75-eb23360fd45b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_real_moment_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original image kth ENNReal moment limits are finite, so their
toReal values converge and can be combined with signed polynomial coefficients. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    Tendsto
      (fun h : ℝ => ((ENNReal.ofReal h)⁻¹ * (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω))))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
          Real.exp)).toReal)) := by
  have hLim :=
    avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image X k
  have hFinite : (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
          Real.exp)) ≠ ⊤ := by
    rw [avram_p2_negative_levy_weighted_exp_real_moment_bridge X k]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.tendsto_toReal hFinite).comp hLim
