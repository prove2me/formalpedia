-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:51:07.203543+00:00
-- url     : https://prove2.me/submissions/d19bd3db-1649-45a4-a54b-6b0efa236693

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- When every actual original jump is zero, its marked source has no atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0)
    (t : ℝ≥0) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = 0 := by
  have hEmpty :
      {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} =
      ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hu
    exact hu.2 (hNoJump u hu.1)
  simp [avram_p4_h_gaussian_intrinsic_large_jump_sum, hEmpty]
