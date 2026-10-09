-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.iUnion_band
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:35:53.684393+00:00
-- url     : https://prove2.me/submissions/389f5dcb-1f91-4f4b-8e91-0565bae749ad

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.iUnion_band
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
import Theorems.Thm_BookProof_EnergyBandDecomposition_mem_band_iff_floor
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (hε : 0 < ε) (E : X → ℝ) : (⋃ k : ℤ, band E ε k) = Set.univ := by

  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨⌊E x / ε⌋, (mem_band_iff_floor hε E _ x).mpr rfl⟩
