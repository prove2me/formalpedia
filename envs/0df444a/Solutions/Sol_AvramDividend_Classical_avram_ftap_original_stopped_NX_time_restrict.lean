-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_stopped_NX_time_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:39:25.142796+00:00
-- url     : https://prove2.me/submissions/8b7c8db5-c104-4b2f-a0e2-c1be40b02b32

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Original stopped jump mark identity adapted from FTAPTheorem42/Foundations/Paths.lean,
commit 8c9c46e1b6e455f7d3069062957d4363879836ce; Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_physical_marked_jump_measure
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_mark_map_measurable
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → ℝ≥0) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
      MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
        Function.leftLim
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
          Function.leftLim
            (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
              (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u))) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u))).restrict
      {p : ℝ≥0 × ℝ | p.1 ≤ τ ω} := by
  rw [avram_ftap_original_stopped_physical_marked_jump_measure X τ ω]
  have hS : MeasurableSet {p : ℝ≥0 × ℝ | p.1 ≤ τ ω} :=
    measurableSet_le measurable_fst measurable_const
  rw [Measure.restrict_map
    (avram_b27_original_intrinsic_mark_map_measurable X ω) hS]
  rfl

