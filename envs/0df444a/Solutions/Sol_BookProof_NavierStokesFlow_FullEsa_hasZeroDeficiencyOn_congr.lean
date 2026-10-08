-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:16:03.053526+00:00
-- url     : https://prove2.me/submissions/09bebb23-6397-4dfe-9494-8cb39b18a8dd

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} {H₁ H₂ : D →ₗ[ℂ] D}
    (h : ∀ x : D, (H₁ x : F) = (H₂ x : F)) (h₁ : HasZeroDeficiencyOn D H₁) :
    HasZeroDeficiencyOn D H₂ := by

  refine ⟨fun w hw => h₁.1 w fun v => ?_, fun w hw => h₁.2 w fun v => ?_⟩ <;>
    · rw [h v]; exact hw v
