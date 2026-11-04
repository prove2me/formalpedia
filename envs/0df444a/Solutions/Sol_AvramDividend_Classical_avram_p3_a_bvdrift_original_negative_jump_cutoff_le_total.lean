-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_negative_jump_cutoff_le_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:18:12.764484+00:00
-- url     : https://prove2.me/submissions/672ea524-a452-4a54-ab2f-9ff8854ea7ed

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Removing small actual source left jumps cannot increase their total
negative-jump magnitude on any sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) (ε : ℝ≥0∞) :
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ ε < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) ≤
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) := by
  classical
  apply ENNReal.tsum_le_tsum
  intro v
  by_cases hε : 0 < v ∧ v ≤ T ∧ ε <
      ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
  · have ht : 0 < v ∧ v ≤ T := ⟨hε.1, hε.2.1⟩
    simp [hε, ht]
  · simp [hε]