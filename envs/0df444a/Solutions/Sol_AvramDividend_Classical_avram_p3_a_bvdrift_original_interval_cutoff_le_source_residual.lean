-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_cutoff_le_source_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:42:48.14792+00:00
-- url     : https://prove2.me/submissions/f745a980-94ea-4393-b3c5-9364ca3a4b0b

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

/-- Any separated actual-source jump cutoff is dominated by the original
bounded-variation drift-minus-path increment on each ordered interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → ∀ ε : ℝ≥0∞,
      (∑' (u : ℝ≥0),
        if s < u ∧ u ≤ t ∧
             ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        then ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by
  classical
  filter_upwards [avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual X hBV] with ω hω
  intro s t hst ε
  calc
    (∑' (u : ℝ≥0),
      if s < u ∧ u ≤ t ∧
          ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      then ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0) ≤
      (∑' (u : ℝ≥0),
        if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) := by
          apply ENNReal.tsum_le_tsum
          intro u
          by_cases hε : s < u ∧ u ≤ t ∧
              ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
          · have ht : s < u ∧ u ≤ t := ⟨hε.1, hε.2.1⟩
            simp [hε, ht]
          · simp [hε]
    _ ≤ _ := hω s t hst
