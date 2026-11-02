-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:26:53.41121+00:00
-- url     : https://prove2.me/submissions/bd497d70-d3cd-4b9f-8e98-4adfb5d74aa6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- An original-source first-moment equality kills the actual downward
BV residual at one fixed horizon. This is a conditional bridge: the
missing intrinsic source jump compensator must supply that equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P,
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
  have hnonneg : 0 ≤ᵐ[P] (fun ω : Ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) := by
    filter_upwards [hsource] with ω hω
    obtain ⟨R, hRdef, _hRzero, _hRmono, hpath⟩ := hω
    change 0 ≤ ((t : ℝ) * X.drift - X.X t ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal
    rw [← hRdef t]
    exact (hpath t).1
  have hzero :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hIntegrable).mp hMeanZero
  filter_upwards [hsource, hzero] with ω hω hωzero
  obtain ⟨R, hRdef, _hRzero, _hRmono, hpath⟩ := hω
  have hRzero : R t = 0 := by
    rw [hRdef t]
    exact hωzero
  simpa [hRzero] using (hpath t).2
