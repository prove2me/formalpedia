-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:26:28.240324+00:00
-- url     : https://prove2.me/submissions/feeafe73-478b-4265-a164-4d33da03f679

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV source starts at zero.  The actual intrinsic negative
mark integral and an explicitly normalised, nonnegative downward residual
then give the complete anchored source path, with positive physical drift
under Standing.  This does not assert that the residual vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    0 < X.drift ∧
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      R 0 = 0 ∧ Monotone R ∧
      ∀ t : ℝ≥0,
        0 ≤ R t ∧
        X.X t ω =
          (t : ℝ) * X.drift -
            (∫⁻ p,
              (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal - R t := by
  refine ⟨(bv_standing_drift_pos X hStanding hBV).1, ?_⟩
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hω
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
    have hr := hRdef 0
    rw [hsumZero] at hr
    simpa [X.X_zero] using hr
  refine ⟨R, hRdef, hRzero, hRmono, ?_⟩
  intro t
  constructor
  · calc
      (0 : ℝ) = R 0 := hRzero.symm
      _ ≤ R t := hRmono (by positivity)
  · have hsource := hinterval 0 t (by positivity)
    simpa [X.X_zero, hRzero] using hsource
