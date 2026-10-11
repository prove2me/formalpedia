-- Prove2me | solution 1 for BookProof.TensorCore.symmetricOn_sectorOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:11.237555+00:00
-- url     : https://prove2.me/submissions/caf34f6c-44fa-493a-a362-009df581eb42

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.symmetricOn_sectorOp
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_sectorOp_apply
import Theorems.Thm_BookProof_TensorCore_derPow_symm
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hA : SymmetricOn D₂ A) (n : ℕ) :
    SymmetricOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n) := by

  intro x y
  obtain ⟨x₀, hx₀⟩ := x.2
  obtain ⟨y₀, hy₀⟩ := y.2
  have hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀ := hx₀.symm
  have hy : (y : Hs.pow n) = inclPow Hs D₂ n y₀ := hy₀.symm
  rw [sectorOp_apply Hs D₂ A n x x₀ hx, sectorOp_apply Hs D₂ A n y y₀ hy, hx, hy]
  exact derPow_symm Hs D₂ A hA n x₀ y₀
