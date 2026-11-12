-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compound_driver_interarrival_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:21:31.220419+00:00
-- url     : https://prove2.me/submissions/472d9c19-7a1a-489c-a970-ca714ad9e62c

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
noncomputable section

/-- Restrict joint interarrival-mark independence along the left-summand embedding. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    iIndepFun τ P := by
  have h : iIndepFun (fun n : ℕ => (Sum.elim τ Y) (Sum.inl n)) P := by
    exact hd.indep.precomp (Sum.inl_injective : Function.Injective (Sum.inl : ℕ → ℕ ⊕ ℕ))
  simpa using h
