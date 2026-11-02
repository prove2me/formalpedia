-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_increment_two_sided_drift_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:53:04.492196+00:00
-- url     : https://prove2.me/submissions/8fa90e18-262d-4062-9ac7-c46e2f533092

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original source BV downward residual is squeezed between zero
and the actual drift-minus-source-path increment, on one a.s. event;
the bound may be used as an integrability envelope without Ito-Meyer. -/
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
      ∀ (s t : ℝ≥0) (hst : s ≤ t),
        0 ≤ R t - R s ∧
          R t - R s ≤
            ((t : ℝ) - (s : ℝ)) * X.drift -
              (X.X t ω - X.X s ω) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro s t hst
  constructor
  · exact sub_nonneg.mpr (hRmono hst)
  have hjump :
      0 ≤ (∑' (v : ℝ≥0),
        if s < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal :=
    ENNReal.toReal_nonneg
  have hsource := hinterval s t hst
  linarith only [hsource, hjump]
