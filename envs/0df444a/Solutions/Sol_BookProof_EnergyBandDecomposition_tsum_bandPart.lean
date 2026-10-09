-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.tsum_bandPart
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:36:34.304305+00:00
-- url     : https://prove2.me/submissions/3585f9f6-141e-45f5-9f5a-e132bdc0f90f

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.tsum_bandPart
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
import Theorems.Thm_BookProof_EnergyBandDecomposition_mem_band_iff_floor
import Theorems.Thm_BookProof_EnergyBandDecomposition_bandPart_of_mem
import Theorems.Thm_BookProof_EnergyBandDecomposition_bandPart_of_not_mem
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution (hε : 0 < ε) (f : X → ℂ) (x : X) :
    ∑' k : ℤ, bandPart E ε k f x = f x := by

  have hsingle : ∀ k : ℤ, k ≠ ⌊E x / ε⌋ → bandPart E ε k f x = 0 := by
    intro k hk
    exact bandPart_of_not_mem (fun hx => hk ((mem_band_iff_floor hε E k x).mp hx)) f
  rw [tsum_eq_single ⌊E x / ε⌋ hsingle]
  exact bandPart_of_mem ((mem_band_iff_floor hε E _ x).mpr rfl) f
