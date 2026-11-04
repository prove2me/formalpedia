-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_kmoment_ennreal_rate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:30:45.136496+00:00
-- url     : https://prove2.me/submissions/9805c923-abf3-457f-be45-38940ab21c33

import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.Tendsto
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_kmoment_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_ennreal_moment_normalised_ofReal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω =>
            ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))) /
          ENNReal.ofReal h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (ENNReal.ofReal (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν))) := by
  let A : ℝ → ℝ≥0∞ := fun h =>
    ∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))
  let L : ℝ := ∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
    (Real.exp (θ * y) - 1) ^ 4 ∂X.ν
  change Tendsto (fun h : ℝ => A h / ENNReal.ofReal h)
    (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (ENNReal.ofReal L))
  have hf (h : ℝ) : A h ≠ ⊤ := by
    exact ne_of_lt
      (AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_kmoment_finite
        X hX (Real.toNNReal h) θ hθ k)
  have hreal : Tendsto (fun h : ℝ => (A h).toReal / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds L) := by
    exact AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
      X hX k θ hθ
  have hcomp : Tendsto (fun h : ℝ => ENNReal.ofReal ((A h).toReal / h))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (ENNReal.ofReal L)) :=
    (ENNReal.continuous_ofReal.tendsto L).comp hreal
  have hp : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h := by
    change Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Ioi 0)
    exact self_mem_nhdsWithin
  have heq : (fun h : ℝ => ENNReal.ofReal ((A h).toReal / h)) =ᶠ[
      nhdsWithin (0 : ℝ) (Ioi 0)] (fun h : ℝ => A h / ENNReal.ofReal h) := by
    filter_upwards [hp] with h hh
    exact AvramDividend.Classical.avram_p2_b_rate_finite_ennreal_moment_normalised_ofReal
      (A h) (hf h) h hh
  exact hcomp.congr' heq
