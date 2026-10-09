-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.measurableSet_band
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:34:57.553102+00:00
-- url     : https://prove2.me/submissions/d03399ee-7a6f-4d83-8ab5-5774664f1c86

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.measurableSet_band
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution [MeasurableSpace X] (hE : Measurable E) (ε : ℝ) (k : ℤ) :
    MeasurableSet (band E ε k) := hE measurableSet_Ico
