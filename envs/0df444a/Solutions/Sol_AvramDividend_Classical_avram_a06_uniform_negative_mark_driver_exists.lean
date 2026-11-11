-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_negative_mark_driver_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:27:39.553603+00:00
-- url     : https://prove2.me/submissions/db66ebf5-310b-4ef4-b1a3-c07e9a4d9fba

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Independent exponential waiting times and continuously distributed
negative marks for a concrete finite-activity jump process. -/
theorem solution :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (τ Y : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  have hν : ν Set.univ = 1 := by
    simp [ν, Measure.restrict_apply_univ, Real.volume_Ioo]
  letI : IsProbabilityMeasure ν := ⟨hν⟩
  simpa only [ν] using
    (levy_foundations_compoundPoissonDriverExists
      (1 : ℝ≥0) (by norm_num) ν)
