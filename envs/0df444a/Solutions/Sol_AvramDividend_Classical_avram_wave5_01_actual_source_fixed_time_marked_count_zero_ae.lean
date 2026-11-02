-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_fixed_time_marked_count_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:02:51.284733+00:00
-- url     : https://prove2.me/submissions/8a7859f2-ec1f-4061-b259-bbe217aa7048

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ht : 0 < t) (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B) = 0 := by
  classical
  filter_upwards [avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae X t ht]
    with ω hω
  rw [avram_wave5_01_actual_source_jump_measure_single_time_atom_exact X ω t B hB]
  have hEmpty :
      {u : ℝ≥0 | u = t ∧ 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B} =
      ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, _, hne, _⟩
    exact hne hω
  simp only [hEmpty, Set.encard_empty]
  norm_num
