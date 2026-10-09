-- Prove2me | solution 1 for BookProof.TwoParticleSector.isReducingProjection_bosonicProj
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:49:17.377893+00:00
-- url     : https://prove2.me/submissions/1edd37bb-3a1c-4965-af24-ad578e329b6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.isReducingProjection_bosonicProj
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_swapH_inner
import Theorems.Thm_BookProof_TwoParticleSector_swapH_involutive
import Theorems.Thm_BookProof_ReducedEsa_isReducingProjection_symProj
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution : IsReducingProjection (bosonicProj Hs) :=
  isReducingProjection_symProj (swapH_involutive Hs)
      (fun x y => swapH_inner Hs x y)
