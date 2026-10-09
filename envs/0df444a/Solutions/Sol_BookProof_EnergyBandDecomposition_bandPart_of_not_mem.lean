-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.bandPart_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:36:33.194977+00:00
-- url     : https://prove2.me/submissions/ebad97a5-2e16-41a8-b37d-a9a2f1914ffb

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.bandPart_of_not_mem
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (hx : x ∉ band E ε k) (f : X → ℂ) :
    bandPart E ε k f x = 0 := Set.indicator_of_notMem hx f
