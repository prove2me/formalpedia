-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compound_raw_independent_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:41:08.095198+00:00
-- url     : https://prove2.me/submissions/2d125293-3578-4595-a75f-e8a190d31de7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_zero_drift_marked_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_increments_add_linear_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    HasIndependentIncrements
      (fun (t : ℝ≥0) ω => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) P := by
  have hmark := avram_a06_original_zero_drift_marked_independent P τ Y hd
  have h := avram_a06_independent_increments_add_linear_drift P
    (fun (t : ℝ≥0) ω =>
      LevyFoundations.piecewisePath 0 0
        (fun n => LevyFoundations.arrival τ n ω)
        (fun n => Y n ω) (t : ℝ)) (1 : ℝ) hmark
  convert h using 1
  ext t ω
  simp only [LevyFoundations.compoundPoisson, LevyFoundations.piecewisePath]
  ring
