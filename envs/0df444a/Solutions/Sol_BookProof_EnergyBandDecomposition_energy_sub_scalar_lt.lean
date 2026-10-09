-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.energy_sub_scalar_lt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:36:07.403016+00:00
-- url     : https://prove2.me/submissions/3ca52234-e1f9-4af3-98bb-f26a91ca3ccd

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.energy_sub_scalar_lt
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (hε : 0 < ε) (hx : x ∈ band E ε k) :
    |E x - k * ε| < ε := by

  obtain ⟨h1, h2⟩ := hx
  rw [abs_lt]
  constructor
  · linarith
  · nlinarith [h2]
