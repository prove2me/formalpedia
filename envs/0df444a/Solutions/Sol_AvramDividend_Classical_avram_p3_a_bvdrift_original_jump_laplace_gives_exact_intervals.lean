-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_laplace_gives_exact_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:54:24.661767+00:00
-- url     : https://prove2.me/submissions/decca1f6-3e40-4def-88a8-adb3c83e6339

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_physical_drift_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_laplace_match_kills_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One authentic original-source jump Laplace functional forces the exact
BV physical-drift path identity on every interval within one horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ)
    (hJInt : Integrable (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal))) P)
    (hJLap : (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
      Real.exp (-(T : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  have hθ0 : 0 ≤ θ := by linarith only [hθ]
  have hXInt :=
    avram_p3_a_bvdrift_original_physical_drift_exponential_integrable
      X hBV T θ hθ0
  have hRzero :=
    avram_p3_a_bvdrift_actual_jump_laplace_match_kills_residual
      X hBV T θ hθ hJInt hXInt hJLap
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV, hRzero] with ω hSource hωzero
  obtain ⟨R, hRdef, hRmono, hRinterval⟩ := hSource
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
  have hRzero : R 0 = 0 := by
    have h := hRdef 0
    rw [hsumZero] at h
    simpa [X.X_zero] using h
  have hRT : R T = 0 := by
    rw [hRdef T]
    exact hωzero
  intro s t hst htT
  have hs : R s = 0 := by
    have hnonneg : 0 ≤ R s := by
      calc (0 : ℝ) = R 0 := hRzero.symm
        _ ≤ R s := hRmono (by positivity)
    have hle := hRmono (hst.trans htT)
    linarith only [hnonneg, hle, hRT]
  have ht : R t = 0 := by
    have hnonneg : 0 ≤ R t := by
      calc (0 : ℝ) = R 0 := hRzero.symm
        _ ≤ R t := hRmono (by positivity)
    have hle := hRmono htT
    linarith only [hnonneg, hle, hRT]
  simpa [hs, ht] using hRinterval s t hst
