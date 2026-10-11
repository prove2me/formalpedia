-- Prove2me | solution 1 for BookProof.TwoParticleSector.derPow_swapDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:00.336179+00:00
-- url     : https://prove2.me/submissions/b4eb5c8b-896a-4ffd-97ee-7e5e6f639b6d

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.derPow_swapDom
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_tensorSquare_induction
import Theorems.Thm_BookProof_TwoParticleSector_derPow_two_tmul
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (t : ((domSpace Hs D₂).pow 2).carrier) :
    derPow Hs D₂ A 2 (swapDom Hs D₂ t) = swapH Hs (derPow Hs D₂ A 2 t) := by

  refine tensorSquare_induction (Y := (D₂ : Type))
    (P := fun t => derPow Hs D₂ A 2 (swapDom Hs D₂ t) = swapH Hs (derPow Hs D₂ A 2 t))
    ?_ ?_ ?_ t
  · simp
  · intro a b c
    rw [swapDom_tmul, derPow_two_tmul, derPow_two_tmul]
    rw [map_add, swapH_tmul, swapH_tmul]
    abel
  · intro u v hu hv
    simp [map_add, hu, hv]
