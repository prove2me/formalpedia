-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_positive_supremum_tail_extend
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:11:24.100246+00:00
-- url     : https://prove2.me/submissions/49599fa1-5004-4846-b0e6-195fd0576a93

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (W : Ω → ENNReal)
    (hSpos : ∀ᵐ z ∂μ, 0 < S z)
    (hPos : ∀ b : ℝ, 0 ≤ b →
      (μ.withDensity W) {z : Ω | b < S z} =
        μ {z : Ω | b < S z} * (∫⁻ z, W z ∂μ)) :
    ∀ b : ℝ,
      (μ.withDensity W) {z : Ω | b < S z} =
        μ {z : Ω | b < S z} * (∫⁻ z, W z ∂μ) := by
  intro b
  rcases le_or_gt 0 b with hb | hb
  · exact hPos b hb
  have hae : {z : Ω | b < S z} =ᵐ[μ] {z : Ω | 0 < S z} := by
    filter_upwards [hSpos] with z hz
    exact propext ⟨fun _ => hz, fun _ => lt_trans hb hz⟩
  have hae' : {z : Ω | b < S z} =ᵐ[μ.withDensity W] {z : Ω | 0 < S z} :=
    (withDensity_absolutelyContinuous μ W).ae_le hae
  rw [measure_congr hae, measure_congr hae']
  exact hPos 0 le_rfl
