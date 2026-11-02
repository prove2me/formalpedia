-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:49:27.827812+00:00
-- url     : https://prove2.me/submissions/ad9752bb-7f00-466a-81fe-bea689496fac

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/--
An actual BV source path has a finite real residual, and the entire
negative source-jump series consumes no more than this residual.
The remainder is nonnegative on every samplewise stopped interval.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ∃ r : ℝ, 0 ≤ r ∧
        (∑' (u : ℝ≥0),
          if s < u ∧ u ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
          else 0).toReal + r =
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual X hBV,
      bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hjumps hmono
  intro s t hst
  let residual : ℝ :=
    ((t : ℝ) * X.drift - X.X t ω) -
      ((s : ℝ) * X.drift - X.X s ω)
  let mass : ℝ≥0∞ :=
    ∑' (u : ℝ≥0),
      if s < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0
  have hres : 0 ≤ residual := by
    change 0 ≤ ((t : ℝ) * X.drift - X.X t ω) -
      ((s : ℝ) * X.drift - X.X s ω)
    exact sub_nonneg.mpr (hmono hst)
  have hbound : mass ≤ ENNReal.ofReal residual := by
    simpa only [mass, residual] using hjumps s t hst
  have hfinite : ENNReal.ofReal residual ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have hreal : mass.toReal ≤ residual := by
    have hh := ENNReal.toReal_mono hfinite hbound
    simpa only [ENNReal.toReal_ofReal hres] using hh
  refine ⟨residual - mass.toReal, by linarith only [hreal], ?_⟩
  change mass.toReal + (residual - mass.toReal) = residual
  ring
