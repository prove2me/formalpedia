-- Prove2me | solution 1 for BookProof.ChapterAbelianGelfandModel.norm_oneVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:48:41.676033+00:00
-- url     : https://prove2.me/submissions/b2a4ca85-5726-4aa1-b20e-1f503cc8e90c

-- Generated from ChapterAbelianGelfandModel.lean — solution of BookProof.ChapterAbelianGelfandModel.norm_oneVec
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_oneVec_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterAbelianGelfandModel



open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {X : Type*} [TopologicalSpace X]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)

set_option maxHeartbeats 1000000 in
theorem solution [IsProbabilityMeasure mu] : ‖oneVec mu‖ = 1 := by

  have h : (inner ℂ (oneVec mu) (oneVec mu) : ℂ) = (1 : ℂ) := by
    rw [L2.inner_def]
    have hone : ∫ _x : X, (1 : ℂ) ∂mu = 1 := by simp
    rw [← hone]
    refine integral_congr_ae ?_
    filter_upwards [oneVec_coeFn mu] with x h1
    simp [h1]
  have h2 : ‖oneVec mu‖ ^ 2 = 1 := by
    have h3 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (oneVec mu)
    rw [h] at h3
    have h4 : ((1 : ℂ)) = ((‖oneVec mu‖ ^ 2 : ℝ) : ℂ) := by simpa using h3
    exact_mod_cast h4.symm
  nlinarith [norm_nonneg (oneVec mu)]
