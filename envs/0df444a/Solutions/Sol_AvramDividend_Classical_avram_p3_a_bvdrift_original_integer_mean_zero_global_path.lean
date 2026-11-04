-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_mean_zero_global_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:22:02.164761+00:00
-- url     : https://prove2.me/submissions/026410a8-0862-4743-ab8d-10369f205d95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV sample path equals its source drift minus genuine negative
left-jump magnitudes at all times, under explicit integer residual means. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hInt : ∀ n : ℕ, Integrable (fun ω : Ω =>
      (((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P)
    (hMean : ∀ n : ℕ, (∫ ω : Ω,
      ((((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by
  have hNat : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∀ s t : ℝ≥0, s ≤ t → t ≤ (n : ℝ≥0) →
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
    intro n
    exact avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
      X hBV (n : ℝ≥0) (hInt n) (hMean n)
  filter_upwards
    [(ae_all_iff.mpr hNat),
     avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
       X hBV] with ω hω hEncoding
  intro t
  obtain ⟨n, htnReal⟩ := exists_nat_ge (t : ℝ)
  have htn : t ≤ (n : ℝ≥0) := by exact_mod_cast htnReal
  have h := hω n 0 t (by positivity) htn
  simp only [NNReal.coe_zero, zero_sub, sub_zero] at h
  rw [X.X_zero ω] at h
  simp only [sub_zero] at h
  rw [← hEncoding t] at h
  exact h
