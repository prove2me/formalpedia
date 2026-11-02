-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_BV_alltime_intrinsic_purejump_from_integer_residual_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:36:31.028676+00:00
-- url     : https://prove2.me/submissions/43ee928c-eb1c-4fec-86c0-f72869436b23

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_BV_intrinsic_pure_jump_all_time_from_integer_horizon_compensator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A countable collection of exact original-source first-moment
normalisations at integer horizons implies the full pure-jump identity
simultaneously at every nonnegative real time. All moment conditions
are explicit premises, not consequences silently asserted from BV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hIntegrable : ∀ n : ℕ, Integrable (fun ω : Ω =>
      (((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : ∀ n : ℕ, (∫ ω : Ω,
      ((((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∫⁻ p,
          (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  apply avram_wave5_04a_original_BV_intrinsic_pure_jump_all_time_from_integer_horizon_compensator
    X hStanding hBV
  intro n
  exact avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
    X hStanding hBV (n : ℝ≥0) (hIntegrable n) (hMeanZero n)
