-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.bandPart_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:36:32.147977+00:00
-- url     : https://prove2.me/submissions/f64dd4ff-5ef6-4a4e-8748-2a6f8814aa35

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.bandPart_of_mem
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (hx : x ∈ band E ε k) (f : X → ℂ) :
    bandPart E ε k f x = f x := Set.indicator_of_mem hx f
