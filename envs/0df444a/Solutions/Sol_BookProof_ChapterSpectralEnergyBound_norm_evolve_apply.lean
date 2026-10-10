-- Prove2me | solution 1 for BookProof.ChapterSpectralEnergyBound.norm_evolve_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:12:45.406296+00:00
-- url     : https://prove2.me/submissions/da9b253f-6b0e-4af0-88f7-6b49dd268a26

-- Generated from ChapterSpectralEnergyBound.lean — solution of BookProof.ChapterSpectralEnergyBound.norm_evolve_apply
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound
open BookProof.ChapterBornMeasure




variable {n : Type*} [Fintype n]

variable {n : Type*} [Fintype n]


@[simp] private theorem evolve_apply (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) :
    evolve f t v i = Complex.exp (-Complex.I * (t : ℂ) * (f i : ℂ)) * v i := rfl

set_option maxHeartbeats 1000000 in
theorem solution (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) :
    ‖evolve f t v i‖ = ‖v i‖ := by

  have habs : ‖Complex.exp (-Complex.I * (t : ℂ) * (f i : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [evolve_apply, norm_mul, habs, one_mul]
