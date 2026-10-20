-- Prove2me | solution 1 for BookProof.TensorCore.isGraphCore_sectorCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:12.129199+00:00
-- url     : https://prove2.me/submissions/d3c1245f-794d-4ea4-a88a-6ce890c4cb53

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.isGraphCore_sectorCore
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_exists_core_approx
import Theorems.Thm_BookProof_TensorCore_sectorOp_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hcore : IsGraphCore D A) (n : ℕ) :
    IsGraphCore (sectorCore Hs D₂ D n) (sectorOp Hs D₂ A n) := by

  intro x ε hε
  obtain ⟨x₀, hx₀⟩ := x.2
  have hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀ := hx₀.symm
  obtain ⟨y₀, hy₀, hy₁, hy₂⟩ := exists_core_approx Hs D₂ A D hcore n x₀ hε
  refine ⟨⟨inclPow Hs D₂ n y₀, ⟨y₀, rfl⟩⟩, ⟨y₀, hy₀, rfl⟩, ?_, ?_⟩
  · simpa [hx] using hy₁
  · rw [sectorOp_apply Hs D₂ A n x x₀ hx,
      sectorOp_apply Hs D₂ A n ⟨inclPow Hs D₂ n y₀, ⟨y₀, rfl⟩⟩ y₀ rfl]
    exact hy₂
