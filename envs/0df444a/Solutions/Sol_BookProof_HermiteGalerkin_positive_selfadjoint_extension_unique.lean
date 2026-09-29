-- Prove2me | solution 1 for BookProof.HermiteGalerkin.positive_selfadjoint_extension_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:58:56.043791+00:00
-- url     : https://prove2.me/submissions/fe24a18a-4a80-4773-9e8c-c4274d1e2e94

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — solution of BookProof.HermiteGalerkin.positive_selfadjoint_extension_unique
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin













open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]









variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (A : F →L[ℂ] F) (hAH : ∀ x : D, A (x : F) = H x)
    (B : (⊤ : Submodule ℂ F) →ₗ[ℂ] F) (hB : IsPositiveSelfAdjointExtension H B) (x : F) :
    B ⟨x, trivial⟩ = A x := by

  -- read `B` as an everywhere-defined linear map
  set B' : F →ₗ[ℂ] F := B.comp (Submodule.topEquiv (R := ℂ) (M := F)).symm.toLinearMap with hB'
  have hB'apply : ∀ y : F, B' y = B ⟨y, trivial⟩ := fun y => rfl
  -- it is symmetric, hence continuous (Hellinger–Toeplitz)
  have hB'sym : B'.IsSymmetric := by
    intro y w
    have := hB.2.1 ⟨y, trivial⟩ ⟨w, trivial⟩
    simpa [hB'apply] using this
  have hB'cont : Continuous B' := hB'sym.continuous
  -- and it agrees with `A` on the dense domain
  have hagree : ∀ y ∈ (D : Set F), B' y = A y := by
    intro y hy
    obtain ⟨h, hval⟩ := hB.1 ⟨y, hy⟩
    rw [hB'apply, hAH ⟨y, hy⟩, ← hval]
  have := Continuous.ext_on hdense hB'cont A.continuous hagree
  exact (hB'apply x) ▸ congrFun this x
