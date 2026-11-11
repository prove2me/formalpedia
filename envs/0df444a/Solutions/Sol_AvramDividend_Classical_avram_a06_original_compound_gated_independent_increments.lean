-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compound_gated_independent_increments
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:13:14.158213+00:00
-- url     : https://prove2.me/submissions/d98c5004-7186-4d05-9e28-df804bf80e7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_raw_independent_increments

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
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (G : Set ((ℕ → ℝ) × (ℕ → ℝ)))
    [DecidablePred (fun ω => ω ∈ G)]
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G) :
    HasIndependentIncrements
      (fun (t : ℝ≥0) ω =>
        if ω ∈ G then LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
        else (0 : ℝ)) P := by
  classical
  let C : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
  let Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => if ω ∈ G then C t ω else 0
  have hsource : HasIndependentIncrements C P :=
    avram_a06_original_compound_raw_independent_increments P τ Y hd
  change HasIndependentIncrements Z P
  intro n grid hmono
  exact ProbabilityTheory.iIndepFun.congr
    (fun i => by
      filter_upwards [hGae] with ω hw
      simp [increment, Z, C, hw])
    (hsource n grid hmono)
