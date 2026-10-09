-- Prove2me | solution 1 for BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:49:17.997978+00:00
-- url     : https://prove2.me/submissions/df8ba7c6-e8a3-46f9-95a2-a5bbae1ad58e

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Theorems.Thm_BookProof_GraphCore_deficiencyTrivialAt_of_bounded_dense
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : D, ‖T x‖ ≤ C * ‖(x : F)‖)
    (hdense : Dense (D : Set F)) :
    EssentiallySelfAdjointOn D T := by

  constructor
  · simpa using deficiencyTrivialAt_of_bounded_dense T hT hC0 hC hdense (d := 1) one_ne_zero
  · simpa using deficiencyTrivialAt_of_bounded_dense T hT hC0 hC hdense (d := -1) (by norm_num)
