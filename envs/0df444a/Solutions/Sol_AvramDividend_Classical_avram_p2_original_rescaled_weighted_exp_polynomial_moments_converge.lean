-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_polynomial_moments_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:08:02.601993+00:00
-- url     : https://prove2.me/submissions/298c4ad3-67d6-4169-b803-f47c78899fa6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_real_moment_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every rescaled source weighted-image polynomial moment converges
to its genuine negative Levy-integral target in ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    Tendsto
      (fun h : ℝ => (ENNReal.ofReal h)⁻¹ *
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (ENNReal.ofReal
        (∫ y in Iio (0 : ℝ), Real.exp ((k : ℝ) * y) *
          (Real.exp y - 1) ^ 4 ∂X.ν))) := by
  have hd :=
    avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
      X (k : ℝ) 1 (by positivity) (by norm_num)
  have hLim :
      Tendsto
        (fun h : ℝ => ENNReal.ofReal
          ((∫ ω, Real.exp ((k : ℝ) * X.X (Real.toNNReal h) ω) *
            (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h))
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (ENNReal.ofReal
          (∫ y in Iio (0 : ℝ), Real.exp ((k : ℝ) * y) *
            (Real.exp y - 1) ^ 4 ∂X.ν))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (by
      simpa only [one_mul] using hd)
  apply hLim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hp
  have hb := avram_p2_original_weighted_exp_real_moment_bridge
    X (Real.toNNReal h) k
  rw [hb, ENNReal.ofReal_div_of_pos hp, div_eq_mul_inv]
  ac_rfl
