-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_stopped_NX_marked_integral_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:18:19.168899+00:00
-- url     : https://prove2.me/submissions/eee90efb-0ca7-4eab-b1b1-dfefc286dc03

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
FTAPTheorem42/Foundations/Paths.lean stopped jump proofs,
commit 8c9c46e1b6e455f7d3069062957d4363879836ce, Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_NX_time_restrict
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → ℝ≥0) (ω : Ω) :
    (∀ f : (ℝ≥0 × ℝ) → ℝ,
      (∫ p, f p ∂((Measure.count.restrict {u : ℝ≥0 |
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
              (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u)))) =
      (∫ p, ({p : ℝ≥0 × ℝ | p.1 ≤ τ ω}).indicator f p
        ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u))))) ∧
    (∀ g : (ℝ≥0 × ℝ) → ℝ≥0∞,
      (∫⁻ p, g p ∂((Measure.count.restrict {u : ℝ≥0 |
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
              (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u)))) =
      (∫⁻ p, ({p : ℝ≥0 × ℝ | p.1 ≤ τ ω}).indicator g p
        ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u))))) := by
  have hS : MeasurableSet {p : ℝ≥0 × ℝ | p.1 ≤ τ ω} :=
    measurableSet_le measurable_fst measurable_const
  constructor
  · intro f
    rw [avram_ftap_original_stopped_NX_time_restrict X τ ω]
    exact (integral_indicator hS).symm
  · intro g
    rw [avram_ftap_original_stopped_NX_time_restrict X τ ω]
    exact (lintegral_indicator hS g).symm

