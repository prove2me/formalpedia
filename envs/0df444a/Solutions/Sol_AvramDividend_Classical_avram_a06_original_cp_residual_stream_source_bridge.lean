-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_residual_stream_source_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:09:49.561015+00:00
-- url     : https://prove2.me/submissions/9cd32eae-3313-483f-8d8e-53bbc80e23f7

import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_stream_identDistrib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Reuse the already proved original residual-stream distribution theorem. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s : ℝ≥0) :
    IdentDistrib
      (fun ω (j : ℕ) =>
        if j = 0 then
          τ (LevyFoundations.jumpCount
            (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)) ω -
          ((s : ℝ) - ∑ i ∈ Finset.range
            (LevyFoundations.jumpCount
              (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)), τ i ω)
        else
          τ (LevyFoundations.jumpCount
            (fun i => LevyFoundations.arrival τ i ω) (s : ℝ) + j) ω)
      (fun ω j => τ j ω) P P := by
  exact AvramDividend.Classical.avram_a06_original_cp_residual_stream_identDistrib
    P τ Y hd s
