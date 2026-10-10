-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.proj_empty
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:36:17.030118+00:00
-- url     : https://prove2.me/submissions/795011d8-f519-4b06-99a8-2623f018a2cd

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.proj_empty
import Mathlib
import Definitions.Def_ChapterMackeyQuasiInvariant
import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_coeFn
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterMackeyQuasiInvariant



open MeasureTheory Measure


variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K))
variable {μ L}

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure X) (f : Lp K 2 μ) :
    proj μ MeasurableSet.empty f = 0 := by

  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ (MeasurableSet.empty (α := X)) f, Lp.coeFn_zero K 2 μ]
    with x e1 e2
  rw [e1, e2]
  simp
