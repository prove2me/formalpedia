-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.band_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:35:52.537991+00:00
-- url     : https://prove2.me/submissions/ba90f8d2-a7a5-4d07-9700-a10de8b00f00

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.band_pairwise_disjoint
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
import Theorems.Thm_BookProof_EnergyBandDecomposition_mem_band_iff_floor
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (hε : 0 < ε) (E : X → ℝ) :
    Pairwise (Function.onFun Disjoint (band E ε)) := by

  intro j k hjk
  rw [Function.onFun, Set.disjoint_left]
  intro x hj hk
  exact hjk (((mem_band_iff_floor hε E j x).mp hj).trans
    ((mem_band_iff_floor hε E k x).mp hk).symm)
