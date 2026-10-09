-- Prove2me | solution 1 for BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:38:59.510994+00:00
-- url     : https://prove2.me/submissions/96fe8547-7695-4619-812d-2debc5a0a8be

-- Generated from ChapterEnergyBoundedEvolution.lean — solution of BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
import Theorems.Thm_BookProof_ChapterEnergyBoundedEvolution_norm_evol_sub_evol_le_ae
open BookProof.ChapterEnergyBoundedEvolution




open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) :
    eLpNorm (evol E t f - evol E s f) 2 μ
      ≤ ENNReal.ofReal (|t - s| * Emax) * eLpNorm f 2 μ := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (norm_evol_sub_evol_le_ae h s t) 2
