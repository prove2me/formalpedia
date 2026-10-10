-- Prove2me | solution 1 for BookProof.TwoParticleSector.derPow_two_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:14:26.599437+00:00
-- url     : https://prove2.me/submissions/683849a7-0a88-47cf-a680-e7b264dbe513

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.derPow_two_tmul
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorCore

noncomputable section


/-! Helper: the elementary-tensor equations of `inclPow` / `derPow`.  The platform's
published `Def_ChapterTensorGraphCore` carries the definitions but not these three `rfl`
equations, and a solution may not rely on unpublished declarations, so they are stated
locally (this file is standalone: top-level `
@[simp] private theorem derPow_zero (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (x : ((domSpace Hs D₂).pow 0)) :
    derPow Hs D₂ A 0 x = 0 := rfl

theorem solution` still follows). -/

@[simp] theorem inclPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (n : ℕ)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b) = (a : Hs.carrier) ⊗ₜ[ℂ] inclPow Hs D₂ n b := rfl

@[simp] theorem derPow_zero (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (x : ((domSpace Hs D₂).pow 0)) :
    derPow Hs D₂ A 0 x = 0 := rfl

@[simp] theorem derPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)
      = (A a) ⊗ₜ[ℂ] inclPow Hs D₂ n b + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A n b := rfl

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (a b : D₂) (c : ℂ) :
    derPow Hs D₂ A 2 (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier)
      = (A a) ⊗ₜ[ℂ] ((b : Hs.carrier) ⊗ₜ[ℂ] c)
        + (a : Hs.carrier) ⊗ₜ[ℂ] ((A b) ⊗ₜ[ℂ] c) := by

  have h1 : derPow Hs D₂ A 2 (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier)
      = (A a) ⊗ₜ[ℂ] inclPow Hs D₂ 1 (b ⊗ₜ[ℂ] c)
        + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A 1 (b ⊗ₜ[ℂ] c) := rfl
  have h2 : inclPow Hs D₂ 1 (b ⊗ₜ[ℂ] c : ((domSpace Hs D₂).pow 1).carrier)
      = (b : Hs.carrier) ⊗ₜ[ℂ] c := rfl
  have h3 : derPow Hs D₂ A 1 (b ⊗ₜ[ℂ] c : ((domSpace Hs D₂).pow 1).carrier)
      = (A b) ⊗ₜ[ℂ] (c : (Hs.pow 0).carrier) := by
    have : derPow Hs D₂ A 1 (b ⊗ₜ[ℂ] c : ((domSpace Hs D₂).pow 1).carrier)
        = (A b) ⊗ₜ[ℂ] inclPow Hs D₂ 0 c
          + (b : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A 0 c := rfl
    rw [this, derPow_zero]
    simp [inclPow]
  rw [h1, h2, h3]
