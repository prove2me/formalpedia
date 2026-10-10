-- Prove2me | solution 1 for BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:18:08.990114+00:00
-- url     : https://prove2.me/submissions/e62ffcb1-ca00-4d87-ad24-accf8cb5ac66

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h : clGraph T₁ = clGraph T₂) : clDom T₁ = clDom T₂ := by

  unfold clDom
  rw [h]
