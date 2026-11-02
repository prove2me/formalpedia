-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_marked_count_clock_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:34:18.838198+00:00
-- url     : https://prove2.me/submissions/0208758b-d79e-48c0-975a-79b42a7272ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Translate an actual marked source-count interval to a relative-time
count on the very same source path and original sample. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) =
    ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
      X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v) ≠ 0 ∧
      X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v) ∈ B}).encard := by
  classical
  let mark : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) u
  let S : Set ℝ≥0 := {u | 0 < u ∧ mark u ≠ 0 ∧
    (u, mark u) ∈ Ioc s (s + T) ×ˢ B}
  let R : Set ℝ≥0 := {v | 0 < v ∧ v ≤ T ∧
    mark (s + v) ≠ 0 ∧ mark (s + v) ∈ B}
  have hSR : S = (fun v : ℝ≥0 => s + v) '' R := by
    ext u
    constructor
    · intro hu
      have hsu : s ≤ u := le_of_lt hu.2.2.1.1
      have hshift : s + (u - s) = u := add_tsub_cancel_of_le hsu
      have hpos : 0 < u - s := tsub_pos_iff_lt.mpr hu.2.2.1.1
      have hbound : u - s ≤ T := by
        have hh := tsub_le_tsub_right hu.2.2.1.2 s
        simpa only [add_tsub_cancel_left] using hh
      refine ⟨u - s, ?_, hshift⟩
      exact ⟨hpos, hbound, by simpa only [hshift] using hu.2.1,
        by simpa only [hshift] using hu.2.2.2⟩
    · rintro ⟨v, hv, rfl⟩
      have hslt : s < s + v := lt_add_of_pos_right s hv.1
      have hbound : s + v ≤ s + T := by
        simpa only [add_comm s] using (add_le_add_left hv.2.1 s)
      exact ⟨lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hslt,
        hv.2.2.1, ⟨⟨hslt, hbound⟩, hv.2.2.2⟩⟩
  have hA : MeasurableSet (Ioc s (s + T) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hcount :=
    avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
      X ω (Ioc s (s + T) ×ˢ B) hA
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ mark u ≠ 0}).map
    (fun u : ℝ≥0 => (u, mark u))) (Ioc s (s + T) ×ˢ B) = R.encard
  have hinj : Function.Injective (fun v : ℝ≥0 => s + v) := by
    intro a b h
    exact add_left_cancel h
  calc
    _ = (S.encard : ℝ≥0∞) := hcount
    _ = (((fun v : ℝ≥0 => s + v) '' R).encard : ℝ≥0∞) :=
      congrArg (fun n : ENat => (n : ℝ≥0∞)) (congrArg Set.encard hSR)
    _ = (R.encard : ℝ≥0∞) :=
      congrArg (fun n : ENat => (n : ℝ≥0∞)) (hinj.encard_image R)
