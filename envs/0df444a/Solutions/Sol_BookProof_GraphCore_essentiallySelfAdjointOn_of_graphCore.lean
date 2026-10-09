-- Prove2me | solution 1 for BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:49:15.998982+00:00
-- url     : https://prove2.me/submissions/31be2899-7ae1-421c-87dc-96b6a905a3bf

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Theorems.Thm_BookProof_GraphCore_deficiencyTrivialAt_of_graphCore
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T)
    (hesa : EssentiallySelfAdjointOn D₂ T) :
    EssentiallySelfAdjointOn D₁ (restrictOp T h) :=
  ⟨deficiencyTrivialAt_of_graphCore T h hcore hesa.1,
      deficiencyTrivialAt_of_graphCore T h hcore hesa.2⟩
