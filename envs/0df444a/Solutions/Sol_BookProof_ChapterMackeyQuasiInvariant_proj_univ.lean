-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.proj_univ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:35:53.094556+00:00
-- url     : https://prove2.me/submissions/a68ee441-9391-4873-890c-5b738fc4711e

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.proj_univ
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
    proj μ MeasurableSet.univ f = f := by

  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ (MeasurableSet.univ (α := X)) f] with x e1
  simp [e1]
