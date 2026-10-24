-- Prove2me | solution 1 for AvramDividend.Classical.shiftedSup_right_continuous_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:36:01.625314+00:00
-- url     : https://prove2.me/submissions/6923541d-8907-4a8b-9146-6da6ed13d888

import Theorems.Thm_AvramDividend_Classical_intervalSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The supremum of shifted Levy increments is right-continuous on nonnegative time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun r : ℝ≥0 =>
          sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
        (Set.Ici t) t := by
  let f : ℝ≥0 → ℝ := fun r => X.X (u + r) ω - X.X u ω
  have hbounded : ∀ t : ℝ≥0, BddAbove (f '' Set.Icc 0 t) := by
    intro t
    obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω (u + t)
    refine ⟨M - X.X u ω, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    apply sub_le_sub_right
    apply hM
    have hrt : u + r ≤ u + t := by
      calc
        u + r = r + u := add_comm u r
        _ ≤ t + u := add_le_add_left hr.2 u
        _ = u + t := add_comm t u
    exact ⟨u + r, ⟨(show (0 : ℝ≥0) ≤ u + r from zero_le), hrt⟩, rfl⟩
  have hright : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t :=
    shiftedLevy_increments_right_continuous X ω u
  have hf : ∀ t : ℝ≥0, Tendsto f (𝓝[≥] t) (𝓝 (f t)) :=
    fun t => (hright t).tendsto
  exact intervalSup_right_continuous_of_right_continuous f hbounded hf
