-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a42_positive_only_spatial_cell_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:07:40.075207+00:00
-- url     : https://prove2.me/submissions/e0e4bf48-c09b-4cff-92f7-7860bb9e749a

import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger76_positive_only_value_masked_physical_source_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ)))
    (E0 E1 Y Z : Ω → ℝ)
    (hE0 : Measurable E0) (hE1 : Measurable E1)
    (hY : Measurable Y) (hZ : Measurable Z)
    (hcell : ∀ᵐ ω ∂ P,
      (E1 ω = E0 ω ∧ Z ω = Y ω) ∨
      (0 < Y ω ∧ 0 < Z ω)) :
    AEStronglyMeasurable
      (fun ω => E1 ω * (w (Z ω) - w (Y ω))) P := by
  classical
  let E : Nat → Ω → ℝ :=
    fun i ω => if i = 0 then E0 ω else E1 ω
  let Y' : Nat → Ω → ℝ := fun _ => Y
  let Z' : Nat → Ω → ℝ := fun _ => Z
  have hEm : ∀ i, Measurable (E i) := by
    intro i
    by_cases hi : i = 0
    · simpa [E, hi] using hE0
    · simpa [E, hi] using hE1
  have hYm : ∀ i, Measurable (Y' i) := fun _ => hY
  have hZm : ∀ i, Measurable (Z' i) := fun _ => hZ
  have hCells : ∀ᵐ ω ∂ P,
      ∀ i ∈ Finset.range (0 + 1),
      (E (i + 1) ω = E i ω ∧
        Z' i ω = Y' i ω) ∨
      (0 < Y' i ω ∧ 0 < Z' i ω) := by
    filter_upwards [hcell] with ω hc
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    simpa [E, Y', Z'] using hc
  have hCellsTime : ∀ᵐ ω ∂ P,
      ∀ i ∈ Finset.range (0 + 1),
      (E (i + 1) ω = E i ω ∧
        Y' i ω = Y' i ω) ∨
      (0 < Y' i ω ∧ 0 < Y' i ω) := by
    filter_upwards [hcell] with ω hc
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    rcases hc with hc | hc
    · left
      constructor
      · simpa [E] using hc.1
      · rfl
    · right
      constructor
      · simpa [Y'] using hc.1
      · simpa [Y'] using hc.1
  have hFull :=
    avram_gledger76_positive_only_value_masked_physical_source_measurable
      w hw 0 E Y' Z' hEm hYm hZm hCells
  have hTime :=
    avram_gledger76_positive_only_value_masked_physical_source_measurable
      w hw 0 E Y' Y' hEm hYm hYm hCellsTime
  have hFull' : AEStronglyMeasurable
      (fun ω => (E1 ω - E0 ω) * w (Y ω) +
        E1 ω * (w (Z ω) - w (Y ω))) P := by
    simpa [E, Y', Z'] using hFull
  have hTime' : AEStronglyMeasurable
      (fun ω => (E1 ω - E0 ω) * w (Y ω)) P := by
    simpa [E, Y'] using hTime
  have hDiff := hFull'.sub hTime'
  convert hDiff using 1
  funext ω
  dsimp
  ring
