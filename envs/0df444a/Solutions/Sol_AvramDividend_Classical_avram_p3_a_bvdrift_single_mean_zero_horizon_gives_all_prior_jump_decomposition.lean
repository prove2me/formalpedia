-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_single_mean_zero_horizon_gives_all_prior_jump_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:14:43.55418+00:00
-- url     : https://prove2.me/submissions/48c69252-a627-4670-b533-634ab8def00a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- An original-source mean-zero residual at one horizon removes the entire
monotone residual on all earlier physical times, almost surely. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      X.X t ω = (t : ℝ) * X.drift -
        (∫⁻ p,
          (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  have hsource :=
    (avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
      X hStanding hBV).2
  have hfixed :=
    avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
      X hStanding hBV T hIntegrable hMeanZero
  filter_upwards [hsource, hfixed] with ω hω hfixedω
  obtain ⟨R, _hRdef, _hRzero, hRmono, hpath⟩ := hω
  intro t ht
  have hRT : R T = 0 := by
    have hTpath := (hpath T).2
    linarith only [hTpath, hfixedω]
  have hRt : R t = 0 := by
    have hnonneg := (hpath t).1
    have hle := hRmono ht
    linarith only [hnonneg, hle, hRT]
  simpa [hRt] using (hpath t).2
