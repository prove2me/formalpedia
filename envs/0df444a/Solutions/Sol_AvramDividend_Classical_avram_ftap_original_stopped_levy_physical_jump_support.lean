-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_stopped_levy_physical_jump_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:54:10.922357+00:00
-- url     : https://prove2.me/submissions/7a1d92e8-0635-4907-a205-533983257a97

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Source: FTAPTheorem42/Foundations/Paths.lean,
stopped physical left-jump cases, commit 8c9c46e1b6e455f7d3069062957d4363879836ce.
Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_before_clock
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_zero_after_clock
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    (MeasureTheory.stoppedProcess X.X τ t ω -
      Function.leftLim
        (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t ≠ 0) ↔
      (t : WithTop ℝ≥0) ≤ τ ω ∧
        (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0) := by
  by_cases h : (t : WithTop ℝ≥0) ≤ τ ω
  · rw [avram_ftap_original_levy_stopped_left_jump_before_clock
        X τ ω t h]
    constructor
    · intro hn
      exact ⟨h, hn⟩
    · intro hn
      exact hn.2
  · have hAfter : τ ω < (t : WithTop ℝ≥0) := lt_of_not_ge h
    rw [avram_ftap_original_levy_stopped_left_jump_zero_after_clock
      X τ ω t hAfter]
    constructor
    · intro hn
      exact (hn rfl).elim
    · rintro ⟨hle, _⟩
      exact (h hle).elim

