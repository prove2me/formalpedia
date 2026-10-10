-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.proj_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:35:14.376241+00:00
-- url     : https://prove2.me/submissions/a5a19146-e5eb-4398-8733-4ff71a25a07e

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.proj_idem
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
theorem solution (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) :
    proj μ hE (proj μ hE f) = proj μ hE f := by

  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ hE (proj μ hE f), proj_coeFn μ hE f] with x e1 e2
  by_cases hx : x ∈ E <;> simp [e1, e2, hx]
