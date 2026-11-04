-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_source_kernel_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:31:59.986603+00:00
-- url     : https://prove2.me/submissions/85612d62-14e8-4de2-b555-18c0ed9dcdd2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact source s-finite marked kernel carries no mass on any
jointly Borel nonnegative-mark region of the original time-mark space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ κ : Kernel Ω (ℝ≥0 × ℝ), IsSFiniteKernel κ ∧
      (∀ ω, κ ω =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∧
      (∀ (ω : Ω) (C : Set (ℝ≥0 × ℝ)), MeasurableSet C →
        C ⊆ (Set.univ ×ˢ Ici (0 : ℝ)) → κ ω C = 0) := by
  classical
  obtain ⟨κ, hSF, hSource⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  refine ⟨κ, hSF, hSource, ?_⟩
  intro ω C hC hNonneg
  have hEmpty :
      C ∩ (Set.univ ×ˢ Iio (0 : ℝ)) = (∅ : Set (ℝ≥0 × ℝ)) := by
    ext z
    constructor
    · intro hz
      have hzNonneg : 0 ≤ z.2 := (hNonneg hz.1).2
      have hzNeg : z.2 < 0 := hz.2.2
      exact False.elim (not_lt_of_ge hzNonneg hzNeg)
    · intro hz
      exact False.elim ((Set.mem_empty_iff_false z).mp hz)
  rw [hSource ω]
  rw [avram_p2_d_future_full_time_mark_negative_support X ω C hC]
  simp only [hEmpty, measure_empty]
