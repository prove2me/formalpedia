-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_small_negative_exp_quotient_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:08:08.200822+00:00
-- url     : https://prove2.me/submissions/182ffa13-6574-44c1-9417-700c08e71253

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_small_exp_remainder_quotient_linear_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exponential convexity and an O(theta) quotient bound imply zero right derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Filter.Tendsto
      (fun θ : ℝ =>
        (∫ z in Ioo (-1 : ℝ) 0,
          (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  obtain ⟨K, hK0, hK⟩ :=
    avram_ja18g_small_exp_remainder_quotient_linear_rate X
  have hθ : Tendsto (fun θ : ℝ => θ) l (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ θ in l, 0 < θ := by
    filter_upwards [self_mem_nhdsWithin] with θ hθpos
    exact hθpos
  have hone : ∀ᶠ θ in l, θ ≤ 1 := by
    filter_upwards [hθ.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with θ hθsmall
    exact hθsmall.le
  have hnonneg (θ : ℝ) :
      0 ≤ ∫ z in Ioo (-1 : ℝ) 0,
        Real.exp (θ * z) - 1 - θ * z ∂X.ν := by
    apply integral_nonneg
    intro z
    change 0 ≤ Real.exp (θ * z) - 1 - θ * z
    rw [sub_sub, sub_nonneg]
    simpa [add_comm] using Real.add_one_le_exp (θ * z)
  have hbound : Tendsto (fun θ : ℝ => θ * K) l (nhds 0) := by
    simpa using hθ.mul_const K
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound
  · filter_upwards [hpos] with θ hθpos
    exact div_nonneg (hnonneg θ) hθpos.le
  · filter_upwards [hpos, hone] with θ hθpos hθone
    exact hK θ hθpos hθone
