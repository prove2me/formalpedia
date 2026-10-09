-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.evolution_preserves_band
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:38:05.722976+00:00
-- url     : https://prove2.me/submissions/cf2050b5-ccb4-4a68-b5d6-963cd1900986

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.evolution_preserves_band
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
import Theorems.Thm_BookProof_EnergyBandDecomposition_bandPart_of_not_mem
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (f : X → ℂ) (k : ℤ) :
    Function.support (fun x => Complex.exp (-(Complex.I * (t * E x))) * bandPart E ε k f x)
      ⊆ band E ε k := by

  intro x hx
  by_contra hmem
  exact hx (by simp [bandPart_of_not_mem hmem f])
