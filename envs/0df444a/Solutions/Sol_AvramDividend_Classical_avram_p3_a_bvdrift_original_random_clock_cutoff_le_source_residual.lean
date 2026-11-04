-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_random_clock_cutoff_le_source_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:47:21.598794+00:00
-- url     : https://prove2.me/submissions/d6cf8237-91ae-4081-9563-565ad85c3f4a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original bounded-variation source jump cutoff is bounded at any two
almost-surely ordered sample-dependent clocks, without adaptedness premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (S U : Ω → ℝ≥0) (hSU : ∀ᵐ ω ∂P, S ω ≤ U ω) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0∞,
      (∑' (u : ℝ≥0),
        if S ω < u ∧ u ≤ U ω ∧
             ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        then ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal
        ((((U ω : ℝ≥0) : ℝ) * X.drift - X.X (U ω) ω) -
          (((S ω : ℝ≥0) : ℝ) * X.drift - X.X (S ω) ω)) := by
  classical
  filter_upwards [avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual X hBV, hSU] with ω hω hst
  intro ε
  calc
    (∑' (u : ℝ≥0),
      if S ω < u ∧ u ≤ U ω ∧
          ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      then ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) ≤
      (∑' (u : ℝ≥0),
        if S ω < u ∧ u ≤ U ω then
          ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) := by
          apply ENNReal.tsum_le_tsum
          intro u
          by_cases hε : S ω < u ∧ u ≤ U ω ∧
              ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
          · have ht : S ω < u ∧ u ≤ U ω := ⟨hε.1, hε.2.1⟩
            simp [hε, ht]
          · simp [hε]
    _ ≤ _ := hω (S ω) (U ω) hst
