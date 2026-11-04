-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.453125+00:00
-- url     : https://prove2.me/submissions/a22c8c09-1412-4068-b66e-5980da6ccf04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV left-jump sum agrees with the actual marked-count integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal =
      (∫⁻ p,
        (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV] with ω hω
  obtain ⟨R, hRdef, _hRmono, hRinterval⟩ := hω
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
  intro t
  have hDef := hRdef t
  have hInt := hRinterval 0 t (by positivity)
  simp only [NNReal.coe_zero, zero_sub, sub_zero] at hInt
  rw [X.X_zero ω, hRzero] at hInt
  simp only [sub_zero] at hInt
  linarith only [hDef, hInt]
