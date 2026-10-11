-- Prove2me | solution 1 for BookProof.TensorCore.exists_ne_zero_mem_sectorCore_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:00:53.649041+00:00
-- url     : https://prove2.me/submissions/8b517af7-0451-43b2-b4d9-7c9ec69e708c

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.exists_ne_zero_mem_sectorCore_one
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_tmul_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterDirectSumEsa
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore
open BookProof.DirectSumEsa

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

theorem solution (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D)
    (ha0 : a ≠ 0) : ∃ x ∈ sectorCore Hs D₂ D 1, x ≠ 0 := by
  refine ⟨inclPow Hs D₂ 1 ((⟨a, hD haD⟩ : D₂) ⊗ₜ[ℂ] (1 : ℂ)),
    ⟨(⟨a, hD haD⟩ : D₂) ⊗ₜ[ℂ] (1 : ℂ),
      tmul_mem_corePow Hs D₂ D (by simpa using haD) (by trivial), rfl⟩, ?_⟩
  have hnorm : ‖inclPow Hs D₂ 1 ((⟨a, hD haD⟩ : D₂) ⊗ₜ[ℂ] (1 : ℂ))‖ = ‖a‖ := by
    rw [inclPow_tmul]
    change ‖a ⊗ₜ[ℂ] inclPow Hs D₂ 0 (1 : ℂ)‖ = ‖a‖
    have h1 : inclPow Hs D₂ 0 (1 : ℂ) = (1 : ℂ) := rfl
    rw [h1, TensorProduct.norm_tmul]
    change ‖a‖ * ‖(1 : ℂ)‖ = ‖a‖
    simp
  intro hzero
  rw [hzero, norm_zero] at hnorm
  exact ha0 (norm_eq_zero.mp hnorm.symm)
