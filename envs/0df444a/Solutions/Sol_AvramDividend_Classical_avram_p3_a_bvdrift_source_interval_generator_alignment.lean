-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_source_interval_generator_alignment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:14:18.185847+00:00
-- url     : https://prove2.me/submissions/1cb0ade8-0eda-45b3-8b89-76b6e251c359

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original-process BV physical generator and intrinsic signed path budget,
with a zero-anchored nonnegative downward residual (not presumed zero). -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      R 0 = 0 ∧ Monotone R ∧ (∀ t : ℝ≥0, 0 ≤ R t) ∧
      ∀ (s t : ℝ≥0), s ≤ t →
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
          (∫⁻ p,
            (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
          (R t - R s) := by
  constructor
  · exact boundedVariation_generator_physical_drift_representation
      X hBV w x hGen
  · filter_upwards
      [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
        X hBV] with ω hω
    obtain ⟨R, hRdef, hRmono, hRinterval⟩ := hω
    have hnone (v : ℝ≥0) : ¬ (0 < v ∧ v ≤ (0 : ℝ≥0)) := by
      intro hv
      exact (not_lt_of_ge hv.2) hv.1
    have hsumZero :
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (0 : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0) = 0 := by
      calc
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (0 : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0) = ∑' (_ : ℝ≥0), (0 : ℝ≥0∞) := by
            apply tsum_congr
            intro v
            exact if_neg (hnone v)
        _ = 0 := by simp
    have hzero : R 0 = 0 := by
      have h := hRdef 0
      rw [hsumZero] at h
      simpa [X.X_zero] using h
    refine ⟨R, hRdef, hzero, hRmono, ?_, hRinterval⟩
    intro t
    calc
      (0 : ℝ) = R 0 := hzero.symm
      _ ≤ R t := hRmono (by positivity)
