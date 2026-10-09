-- Prove2me | solution 1 for BookProof.GraphCore.IsGraphCore.refl
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:48:24.990445+00:00
-- url     : https://prove2.me/submissions/b5b83568-c547-4ee0-92aa-3b60ab29982a

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.IsGraphCore.refl
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) : IsGraphCore D₂ T := fun x ε hε => ⟨x, x.2, by simpa using hε, by simpa using hε⟩
