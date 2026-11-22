-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_stopped_physical_jump_count_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:05:43.078882+00:00
-- url     : https://prove2.me/submissions/387f6731-99e8-4590-80ff-fe0507d11024

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from FTAPTheorem42/Foundations/Paths.lean original stopped left-jump cases,
commit 8c9c46e1b6e455f7d3069062957d4363879836ce. Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_levy_physical_jump_support
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → ℝ≥0) (ω : Ω) :
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
      MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
        Function.leftLim
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u ≠ 0}) =
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).restrict
      (Iic (τ ω)) := by
  have hSet :
      {u : ℝ≥0 | 0 < u ∧
        MeasureTheory.stoppedProcess X.X
            (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
          Function.leftLim
            (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
              (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u ≠ 0} =
      Iic (τ ω) ∩ {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Iic]
    rw [avram_ftap_original_stopped_levy_physical_jump_support
      X (fun ω => (τ ω : WithTop ℝ≥0)) ω u]
    constructor
    · rintro ⟨hpos, hclock, hjump⟩
      exact ⟨WithTop.coe_le_coe.mp hclock, hpos, hjump⟩
    · rintro ⟨hclock, hpos, hjump⟩
      exact ⟨hpos, WithTop.coe_le_coe.mpr hclock, hjump⟩
  rw [Measure.restrict_restrict measurableSet_Iic]
  exact congrArg (fun S : Set ℝ≥0 => Measure.count.restrict S) hSet

