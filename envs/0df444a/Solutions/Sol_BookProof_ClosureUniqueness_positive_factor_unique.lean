-- Prove2me | solution 1 for BookProof.ClosureUniqueness.positive_factor_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:19:38.870986+00:00
-- url     : https://prove2.me/submissions/f4bb79e4-c967-4feb-95f4-28c7d4dfe3e5

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.positive_factor_unique
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}
open ContinuousLinearMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (B C : H →L[ℂ] H) (hB : B.IsPositive) (hC : C.IsPositive)
    (h : B ∘L B = C ∘L C) : B = C := by

  have hB' : (0 : H →L[ℂ] H) ≤ B := (nonneg_iff_isPositive B).mpr hB
  have hC' : (0 : H →L[ℂ] H) ≤ C := (nonneg_iff_isPositive C).mpr hC
  have hsB : star B = B := hB.isSelfAdjoint
  have hsC : star C = C := hC.isSelfAdjoint
  have hBB : (0 : H →L[ℂ] H) ≤ B * B := by
    have := star_mul_self_nonneg B; rwa [hsB] at this
  have hCC : (0 : H →L[ℂ] H) ≤ C * C := by
    have := star_mul_self_nonneg C; rwa [hsC] at this
  have h1 : CFC.sqrt (B * B) = B := (CFC.sqrt_eq_iff (B * B) B hBB hB').2 rfl
  have h2 : CFC.sqrt (C * C) = C := (CFC.sqrt_eq_iff (C * C) C hCC hC').2 rfl
  have hmul : B * B = C * C := h
  rw [← h1, ← h2, hmul]
