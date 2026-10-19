-- Prove2me | solution 1 for BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:46.559764+00:00
-- url     : https://prove2.me/submissions/cf5137a4-b8e5-4978-8de9-aa4be711ad91

-- Generated from ChapterSpectralEnergyBound.lean — solution of BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Theorems.Thm_BookProof_ChapterSpectralEnergyBound_norm_evolve
import Theorems.Thm_BookProof_ChapterSpectralEnergyBound_evolve_support
import Theorems.Thm_BookProof_ChapterSpectralEnergyBound_norm_diagOp_le
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound




variable {n : Type*} [Fintype n]

variable {n : Type*} [Fintype n]

set_option maxHeartbeats 1000000 in
theorem solution (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n)
    (h : ∀ i, v i ≠ 0 → |f i| ≤ E) (t : ℝ) :
    ‖-Complex.I • diagOp f (evolve f t v)‖ ≤ E * ‖v‖ := by

  have hsupp : ∀ i, evolve f t v i ≠ 0 → |f i| ≤ E := fun i hi =>
    h i (evolve_support f t v i hi)
  have hbound := norm_diagOp_le f E (evolve f t v) hsupp
  rw [norm_smul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  rw [norm_evolve] at hbound
  exact hbound
