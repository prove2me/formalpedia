-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_stopped_physical_marked_jump_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:09:38.11462+00:00
-- url     : https://prove2.me/submissions/fd63eea6-3d6e-44ba-ac37-dfab82f2c116

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adaptation of FTAPTheorem42/Foundations/Paths.lean stopped jump-size calculation,
commit 8c9c46e1b6e455f7d3069062957d4363879836ce. Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_physical_jump_count_measure
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_before_clock
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
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).restrict
        (Iic (τ ω))).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)) := by
  rw [avram_ftap_original_stopped_physical_jump_count_measure X τ ω]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ :=
    Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0})
      measurableSet_Iic] with u hu
  exact congrArg (fun z : ℝ => (u, z))
    (avram_ftap_original_levy_stopped_left_jump_before_clock
      X (fun ω => (τ ω : WithTop ℝ≥0)) ω u
      (WithTop.coe_le_coe.mpr hu))

