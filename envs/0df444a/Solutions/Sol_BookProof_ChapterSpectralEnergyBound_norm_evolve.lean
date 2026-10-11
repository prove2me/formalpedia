-- Prove2me | solution 1 for BookProof.ChapterSpectralEnergyBound.norm_evolve
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:17.051979+00:00
-- url     : https://prove2.me/submissions/9852e2fe-120b-43a8-a948-be0351a15028

-- Generated from ChapterSpectralEnergyBound.lean — solution of BookProof.ChapterSpectralEnergyBound.norm_evolve
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Theorems.Thm_BookProof_ChapterSpectralEnergyBound_norm_evolve_apply
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound




variable {n : Type*} [Fintype n]

variable {n : Type*} [Fintype n]

set_option maxHeartbeats 1000000 in
theorem solution (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) :
    ‖evolve f t v‖ = ‖v‖ := by

  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [norm_evolve_apply]
