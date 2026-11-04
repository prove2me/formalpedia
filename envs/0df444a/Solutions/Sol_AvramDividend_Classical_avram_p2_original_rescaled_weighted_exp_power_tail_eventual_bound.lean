-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_power_tail_eventual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:21:56.515189+00:00
-- url     : https://prove2.me/submissions/277c833b-63c7-416a-bf0b-d63c407ae70d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
import Theorems.Thm_AvramDividend_Classical_avram_p2_nonnegative_power_tail_markov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every source-image high-power rescaled tail is eventually smaller
than any strict upper bound on its genuine Levy-image kth moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) (R : ℝ) (hR : 0 ≤ R) (c : ℝ≥0∞)
    (hc : (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) < c) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal (R ^ k) * ((ENNReal.ofReal h)⁻¹ *
        ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω))) (Ici R)) < c := by
  have hMom :=
    avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image X k
  have hEv : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (ENNReal.ofReal h)⁻¹ *
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))) < c :=
    hMom.eventually (Iio_mem_nhds hc)
  filter_upwards [hEv] with h hh
  let μ : Measure ℝ :=
    ((P.withDensity (fun ω => ENNReal.ofReal
      ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
      (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
  have hMarkov := avram_p2_nonnegative_power_tail_markov μ R hR k
  change ENNReal.ofReal (R ^ k) *
    ((ENNReal.ofReal h)⁻¹ * μ (Ici R)) < c
  calc
    _ = (ENNReal.ofReal h)⁻¹ *
        (ENNReal.ofReal (R ^ k) * μ (Ici R)) := by ac_rfl
    _ ≤ (ENNReal.ofReal h)⁻¹ *
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μ) := by
          exact mul_le_mul_right hMarkov _
    _ < c := by simpa [μ] using hh
