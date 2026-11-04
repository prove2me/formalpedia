-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_mass_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:49:04.888333+00:00
-- url     : https://prove2.me/submissions/0448ab73-64f9-489a-8bb1-d9168047617a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_moment_rate_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto (fun h : ℝ => (((P.withDensity (fun ω =>
          ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω))) Set.univ).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hderiv :=
    AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
      X hX 0 θ hθ
  have hzero : Tendsto (fun h : ℝ => h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hmul := hderiv.mul hzero
  have hlim : Tendsto
      (fun h : ℝ => ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ 0) ∂((P.withDensity (fun ω =>
          ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))).toReal / h) * h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa using hmul
  have hp : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), h ≠ 0 := by
    have hh : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h := by
      change Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Ioi 0)
      exact self_mem_nhdsWithin
    filter_upwards [hh] with h hh
    exact ne_of_gt hh
  apply hlim.congr'
  filter_upwards [hp] with h hh
  simp [div_mul_cancel₀ _ hh]
