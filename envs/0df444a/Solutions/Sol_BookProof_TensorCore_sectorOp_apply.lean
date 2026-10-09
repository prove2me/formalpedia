-- Prove2me | solution 1 for BookProof.TensorCore.sectorOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:49:27.790922+00:00
-- url     : https://prove2.me/submissions/61df318e-7a12-4c5e-981d-b65d7c9bf796

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.sectorOp_apply
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (x : sectorDom Hs D₂ n) (x₀ : ((domSpace Hs D₂).pow n))
    (hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀) :
    sectorOp Hs D₂ A n x = derPow Hs D₂ A n x₀ := by

  have hxx : (LinearEquiv.ofInjective (inclPow Hs D₂ n).toLinearMap
      (inclPow Hs D₂ n).injective) x₀ = x := by
    apply Subtype.ext; rw [hx]; rfl
  have h2 : (LinearEquiv.ofInjective (inclPow Hs D₂ n).toLinearMap
      (inclPow Hs D₂ n).injective).symm x = x₀ := by
    rw [← hxx]; simp
  exact congrArg (fun z => derPow Hs D₂ A n z) h2
