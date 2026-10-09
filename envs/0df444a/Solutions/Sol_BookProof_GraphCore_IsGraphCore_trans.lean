-- Prove2me | solution 1 for BookProof.GraphCore.IsGraphCore.trans
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:48:37.990499+00:00
-- url     : https://prove2.me/submissions/96c6fe16-2407-4905-a404-dba8e84f0dd8

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.IsGraphCore.trans
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D₁ D₂ D₃ : Submodule ℂ F} {T : D₃ →ₗ[ℂ] F}
    (h₂₃ : D₂ ≤ D₃) (h₁ : IsGraphCore D₁ (restrictOp T h₂₃)) (h₂ : IsGraphCore D₂ T) :
    IsGraphCore D₁ T := by

  intro x ε hε
  obtain ⟨y, hyD₂, hy₁, hy₂⟩ := h₂ x (ε / 2) (by positivity)
  obtain ⟨z, hzD₁, hz₁, hz₂⟩ := h₁ ⟨(y : F), hyD₂⟩ (ε / 2) (by positivity)
  refine ⟨⟨(z : F), h₂₃ z.2⟩, hzD₁, ?_, ?_⟩
  · calc ‖(x : F) - (z : F)‖ ≤ ‖(x : F) - (y : F)‖ + ‖(y : F) - (z : F)‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub (x : F) (y : F) (z : F)
      _ < ε / 2 + ε / 2 := by exact add_lt_add hy₁ hz₁
      _ = ε := by ring
  · have hzz : T ⟨(z : F), h₂₃ z.2⟩ = restrictOp T h₂₃ z := rfl
    have hyy : restrictOp T h₂₃ ⟨(y : F), hyD₂⟩ = T y := rfl
    calc ‖T x - T ⟨(z : F), h₂₃ z.2⟩‖
        ≤ ‖T x - T y‖ + ‖T y - T ⟨(z : F), h₂₃ z.2⟩‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub (T x) (T y) (T ⟨(z : F), h₂₃ z.2⟩)
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add hy₂ ?_
          rw [hzz, ← hyy]
          exact hz₂
      _ = ε := by ring
