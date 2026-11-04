-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_negative_jump_cutoff_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:18:10.111749+00:00
-- url     : https://prove2.me/submissions/5008f6ce-ce0d-46e5-9572-be6088c960dc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual source negative-jump magnitude series is antitone in the
lower cutoff: decreasing the cutoff can only include more source jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) (ε₁ ε₂ : ℝ≥0∞) (hε : ε₁ ≤ ε₂) :
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ ε₂ < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) ≤
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ ε₁ < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) := by
  classical
  apply ENNReal.tsum_le_tsum
  intro v
  by_cases h₂ : 0 < v ∧ v ≤ T ∧ ε₂ <
      ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
  · have h₁ : 0 < v ∧ v ≤ T ∧ ε₁ <
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) :=
      ⟨h₂.1, h₂.2.1, lt_of_le_of_lt hε h₂.2.2⟩
    simp [h₂, h₁]
  · simp [h₂]