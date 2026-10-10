-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:36:42.678275+00:00
-- url     : https://prove2.me/submissions/20bafa6a-9e84-4844-9723-6c6815dccfd4

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.proj_add_of_disjoint
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
theorem solution (μ : Measure X) {E F : Set X} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (hd : Disjoint E F) (f : Lp K 2 μ) :
    proj μ (hE.union hF) f = proj μ hE f + proj μ hF f := by

  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ (hE.union hF) f, proj_coeFn μ hE f, proj_coeFn μ hF f,
    Lp.coeFn_add (proj μ hE f) (proj μ hF f)] with x e1 e2 e3 e4
  simp only [Pi.add_apply] at e4
  rw [e1, e4, e2, e3]
  by_cases hx : x ∈ E
  · have hy : x ∉ F := Set.disjoint_left.mp hd hx
    simp [hx, hy]
  · by_cases hy : x ∈ F <;> simp [hx, hy]
