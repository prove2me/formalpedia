-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward61_original_intrinsic_closed_positive_time_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:10:58.236595+00:00
-- url     : https://prove2.me/submissions/ae7fa83d-5aeb-4f84-b897-45ee96804df9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Icc 0 T ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc 0 T ×ˢ B) := by
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hzero : NX ({(0 : ℝ≥0)} ×ˢ B) = 0 :=
    avram_wave5_01_actual_source_jump_measure_zero_initial_time X ω B hB
  have hSet : (Ioc (0 : ℝ≥0) T ×ˢ B) ∪ ({0} ×ˢ B) =
      (Icc (0 : ℝ≥0) T ×ˢ B) := by
    rw [← Set.union_prod, Set.Ioc_union_left (show (0 : ℝ≥0) ≤ T from zero_le)]
  change NX (Icc 0 T ×ˢ B) = NX (Ioc 0 T ×ˢ B)
  apply le_antisymm
  · calc
      NX (Icc 0 T ×ˢ B) = NX ((Ioc 0 T ×ˢ B) ∪ ({0} ×ˢ B)) := by rw [hSet]
      _ ≤ NX (Ioc 0 T ×ˢ B) + NX ({0} ×ˢ B) := measure_union_le _ _
      _ = NX (Ioc 0 T ×ˢ B) := by rw [hzero, add_zero]
  · exact measure_mono (by
      intro p hp
      exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, hp.2⟩)
