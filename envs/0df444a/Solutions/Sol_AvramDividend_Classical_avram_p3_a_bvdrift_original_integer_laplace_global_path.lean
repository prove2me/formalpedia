-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_laplace_global_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:25:26.201897+00:00
-- url     : https://prove2.me/submissions/90046cf1-a194-4a0a-abb1-e81a3d3459d1

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_laplace_global_intervals
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Same-space original BV path equals source generator drift minus its entire
actual negative-left-jump sum, globally on one full-measure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (hLap : ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        Real.exp (-(((n : ℝ≥0) : ℝ) *
          (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by
  have hAll :=
    avram_p3_a_bvdrift_original_integer_laplace_global_intervals
      X hBV θ hθ hLap
  filter_upwards
    [hAll, avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
      X hBV] with ω hIntervals hEncoding
  intro t
  have h := hIntervals 0 t (by positivity)
  simp only [NNReal.coe_zero, zero_sub, sub_zero] at h
  rw [X.X_zero ω] at h
  simp only [sub_zero] at h
  rw [← hEncoding t] at h
  exact h
