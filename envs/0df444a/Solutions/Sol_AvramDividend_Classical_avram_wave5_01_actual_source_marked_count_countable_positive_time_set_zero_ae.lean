-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_marked_count_countable_positive_time_set_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:03:37.28051+00:00
-- url     : https://prove2.me/submissions/ed92e23e-7ac4-45b8-abcb-689503054d9d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set ℝ≥0) (hC : C.Countable) (hPos : ∀ u ∈ C, 0 < u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (C ×ˢ B) = 0 := by
  classical
  haveI : Countable C := hC.to_subtype
  have hAe : ∀ᵐ ω ∂P, ∀ c : C,
      X.X (c : ℝ≥0) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) (c : ℝ≥0) = 0 := by
    apply (ae_all_iff).2
    intro c
    exact avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
      X (c : ℝ≥0) (hPos (c : ℝ≥0) c.property)
  filter_upwards [hAe] with ω hω
  rw [avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
    X ω (C ×ˢ B) (hC.measurableSet.prod hB)]
  have hEmpty :
      {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∈
          C ×ˢ B} = ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, hne, hp⟩
    have hc : u ∈ C := (Set.mem_prod.mp hp).1
    exact hne (hω ⟨u, hc⟩)
  simp only [hEmpty, Set.encard_empty]
  norm_num
