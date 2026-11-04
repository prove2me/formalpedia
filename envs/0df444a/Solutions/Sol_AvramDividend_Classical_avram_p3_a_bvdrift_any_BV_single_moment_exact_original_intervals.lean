-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:37:15.568544+00:00
-- url     : https://prove2.me/submissions/889ec149-e52b-4af1-8c2c-49ea454e683a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any original BV source has exact drift-minus-jumps increments on [0,T]
once the original nonnegative residual has integrable mean zero at T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0) :
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
  have hnonneg : 0 ≤ᵐ[P] (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) := by
    filter_upwards
      [avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
        X hBV,
       avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
        X hBV] with ω hBound hEncoding
    have hb := hBound 0 T (by positivity)
    have he := hEncoding T
    simp only [NNReal.coe_zero, zero_sub, sub_zero] at hb
    rw [X.X_zero ω] at hb
    simp only [sub_zero] at hb
    change 0 ≤ ((T : ℝ) * X.drift - X.X T ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal
    linarith only [hb, he]
  have hzero :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hIntegrable).mp hMeanZero
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV, hzero] with ω hSource hωzero
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
