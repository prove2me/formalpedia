-- Prove2me | solution 1 for BookProof.TensorCore.derPow_symm_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:00:42.569465+00:00
-- url     : https://prove2.me/submissions/5e2b7cd4-36dc-4c93-b6e9-3e6fb46b8ff6

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.derPow_symm_tmul
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_inner_tmul_pow
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

/-! Helper: the elementary-tensor equations of `inclPow` / `derPow`.  The platform's
published `Def_ChapterTensorGraphCore` carries the definitions but not these three `rfl`
equations, and a solution may not rely on unpublished declarations, so they are stated
locally as `private` declarations, so the file is standalone.
-/

@[simp] private theorem inclPow_tmul (n : ℕ)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b) = (a : Hs.carrier) ⊗ₜ[ℂ] inclPow Hs D₂ n b := rfl

@[simp] private theorem derPow_tmul (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)
      = (A a) ⊗ₜ[ℂ] inclPow Hs D₂ n b + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A n b := rfl

theorem solution (hA : SymmetricOn D₂ A) (n : ℕ)
    (ih : ∀ x y : ((domSpace Hs D₂).pow n),
      (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ)
        = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y))
    (a c : D₂) (b d : ((domSpace Hs D₂).pow n)) :
    (inner ℂ (derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)) (inclPow Hs D₂ (n + 1) (c ⊗ₜ[ℂ] d)) : ℂ)
      = inner ℂ (inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b)) (derPow Hs D₂ A (n + 1) (c ⊗ₜ[ℂ] d)) := by
  rw [derPow_tmul, inclPow_tmul, inclPow_tmul, derPow_tmul]
  rw [inner_add_left, inner_add_right]
  rw [inner_tmul_pow Hs n (A a) ((c : Hs.carrier)),
    inner_tmul_pow Hs n ((a : Hs.carrier)) ((c : Hs.carrier)),
    inner_tmul_pow Hs n ((a : Hs.carrier)) (A c),
    inner_tmul_pow Hs n ((a : Hs.carrier)) ((c : Hs.carrier)),
    hA a c, ih b d]
