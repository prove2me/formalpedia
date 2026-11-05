-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_all_lintegral_tendsto_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:06:15.237628+00:00
-- url     : https://prove2.me/submissions/c7c3cf6a-387c-44e3-8d1b-ebef23f7b4e4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_real_lintegral_conversion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem solution
    {ι : Type*} (l : Filter ι) (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 ≤ z)
    (hpositive_μ : ∀ᵐ z ∂μ, 0 ≤ z)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hfinite : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ))) :
    ∀ k, Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
      (nhds (∫ z : ℝ, z ^ k ∂μ)) := by
  intro k
  have hlim :=
    (ENNReal.tendsto_toReal (hfinite k)).comp (hmom k)
  have hEq_i (i : ι) :
      (∫ z : ℝ, z ^ k ∂μi i) =
        (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i).toReal :=
    AvramDividend.Classical.avram_p2_i_moment_real_lintegral_conversion
      (μi i) (hpositive_i i) k (hi i k)
  have hEq_μ :
      (∫ z : ℝ, z ^ k ∂μ) =
        (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ).toReal :=
    AvramDividend.Classical.avram_p2_i_moment_real_lintegral_conversion
      μ hpositive_μ k (hμ k)
  simpa only [Function.comp_def, hEq_i, hEq_μ] using hlim
