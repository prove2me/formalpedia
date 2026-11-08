-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn9_cadlag_true_mark_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:52:07.89788+00:00
-- url     : https://prove2.me/submissions/ec362454-c59b-40a1-b33a-3b244fe20625

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Countably many nonzero jumps make the true mark map a countable
modification of the continuous baseline u ↦ (u, 0). -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) :
    Measurable (fun u : ℝ≥0 =>
      (u, Y u - Function.leftLim Y u)) ∧
    MeasurableSet {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0} := by
  classical
  let jump : ℝ≥0 → ℝ := fun u =>
    Y u - Function.leftLim Y u
  let S : Set ℝ≥0 := {u | 0 < u ∧ jump u ≠ 0}
  obtain ⟨time, mark, hTime, hMark, hCandidate⟩ :=
    avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
  have hCover : S ⊆ Set.range (fun k : ℕ => time k Y) := by
    intro u hu
    obtain ⟨_, hAll⟩ := hCandidate Y hRight hLeft
    exact hAll u hu.1 hu.2
  have hCount : S.Countable :=
    (Set.countable_range (fun k : ℕ => time k Y)).mono hCover
  have hException :
      Set.Countable {u : ℝ≥0 |
        (u, (0 : ℝ)) ≠ (u, jump u)} := by
    apply (hCount.union (Set.countable_singleton (0 : ℝ≥0))).mono
    intro u hu
    by_cases h0 : u = 0
    · exact Or.inr h0
    · apply Or.inl
      constructor
      · exact lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ u) (Ne.symm h0)
      · intro hj
        apply hu
        simp [hj]
  have hBase : Measurable (fun u : ℝ≥0 =>
      (u, (0 : ℝ))) := measurable_id.prodMk measurable_const
  have hMap : Measurable (fun u : ℝ≥0 =>
      (u, jump u)) :=
    hBase.measurable_of_countable_ne hException
  exact ⟨hMap, hCount.measurableSet⟩
