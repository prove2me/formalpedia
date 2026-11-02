-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:33:46.992804+00:00
-- url     : https://prove2.me/submissions/5e86d7a9-c7da-4fd8-8f4a-f2cf585cad74

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (τ : Ω → ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞)
    (hH : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H)
    (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      (if s < p.1 ∧ p.1 ≤ t ∧ p.1 ≤ τ ω ∧ p.2 ∈ B
        then H ((p.1, ω), p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' u : ℝ≥0,
      if 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
        (if s < u ∧ u ≤ t ∧ u ≤ τ ω ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ∈ B
          then H ((u, ω),
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)
          else 0)
      else 0 := by
  let f : (ℝ≥0 × ℝ) → ℝ≥0∞ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.1 ≤ τ ω ∧ p.2 ∈ B
    then H ((p.1, ω), p.2) else 0
  have hLift : Measurable (fun p : ℝ≥0 × ℝ =>
      H ((p.1, ω), p.2)) :=
    hH.comp (avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω)
  have hC : MeasurableSet
      {p : ℝ≥0 × ℝ |
        s < p.1 ∧ p.1 ≤ t ∧ p.1 ≤ τ ω ∧ p.2 ∈ B} := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_fst measurable_const).inter
          (hB.preimage measurable_snd)))
  have hf : Measurable f := hLift.ite hC measurable_const
  exact avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum X ω f hf
