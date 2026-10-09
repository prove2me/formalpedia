-- Prove2me | solution 1 for BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:38:19.677591+00:00
-- url     : https://prove2.me/submissions/6661f8f1-240b-4432-9f8d-1efff37f6462

-- Generated from ChapterEnergyBoundedEvolution.lean — solution of BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
import Theorems.Thm_BookProof_ChapterEnergyBoundedEvolution_norm_evol_apply
open BookProof.ChapterEnergyBoundedEvolution




open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (f : X → ℂ) (p : ℝ≥0∞) :
    eLpNorm (evol E t f) p μ = eLpNorm f p μ := by

  refine eLpNorm_congr_norm_ae ?_
  exact Filter.Eventually.of_forall fun x => norm_evol_apply t f x
