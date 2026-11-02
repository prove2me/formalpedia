-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_source_weighted_remainder_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:23.926859+00:00
-- url     : https://prove2.me/submissions/70342465-7ca8-4496-96d3-8e307ec93ac0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_uniform_stopped_horizon_weighted_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On every stopped increasing partition, the original BV source
remainder has a weighted-variation envelope involving only the source
path and its drift at the samplewise stopping horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ i : ℕ, |a i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i)))| ≤
          M * (((τ ω : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (τ ω) ω - X.X (u 0) ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_remainder_uniform_stopped_horizon_weighted_bound
      X hBV,
      avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV] with ω hweighted hsource
  obtain ⟨R, hRdef, hRmono, hbound⟩ := hweighted
  obtain ⟨Q, hQdef, hQmono, hinterval⟩ := hsource
  have hRQ : R = Q := by
    funext t
    exact (hRdef t).trans (hQdef t).symm
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop a M hM ha
  have hstart : u 0 ≤ τ ω := (hu (Nat.zero_le n)).trans hstop
  have hsourceEq := hinterval (u 0) (τ ω) hstart
  rw [← hRQ] at hsourceEq
  have hjump :
      0 ≤ (∑' (v : ℝ≥0),
        if u 0 < v ∧ v ≤ τ ω then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal :=
    ENNReal.toReal_nonneg
  calc
    |(Finset.range n).sum (fun i =>
        a i * (R (u (i + 1)) - R (u i)))| ≤
        M * (R (τ ω) - R (u 0)) :=
          hbound τ u hu n hstop a M hM ha
    _ ≤ M * (((τ ω : ℝ) - (u 0 : ℝ)) * X.drift -
        (X.X (τ ω) ω - X.X (u 0) ω)) := by
          apply mul_le_mul_of_nonneg_left _ hM
          linarith only [hsourceEq, hjump]
