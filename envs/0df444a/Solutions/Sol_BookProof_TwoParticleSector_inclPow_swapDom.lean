-- Prove2me | solution 1 for BookProof.TwoParticleSector.inclPow_swapDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:58.848642+00:00
-- url     : https://prove2.me/submissions/2a377b71-49bf-4d7f-98d5-add25a0188f1

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.inclPow_swapDom
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_tensorSquare_induction
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

set_option maxHeartbeats 1000000 in
theorem solution (t : ((domSpace Hs D₂).pow 2).carrier) :
    inclPow Hs D₂ 2 (swapDom Hs D₂ t) = swapH Hs (inclPow Hs D₂ 2 t) := by

  refine tensorSquare_induction (Y := (D₂ : Type))
    (P := fun t => inclPow Hs D₂ 2 (swapDom Hs D₂ t) = swapH Hs (inclPow Hs D₂ 2 t))
    ?_ ?_ ?_ t
  · simp
  · intro a b c
    have h1 : inclPow Hs D₂ 2 (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier)
        = (a : Hs.carrier) ⊗ₜ[ℂ] ((b : Hs.carrier) ⊗ₜ[ℂ] c) := rfl
    have h2 : inclPow Hs D₂ 2 (b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier)
        = (b : Hs.carrier) ⊗ₜ[ℂ] ((a : Hs.carrier) ⊗ₜ[ℂ] c) := rfl
    rw [swapDom_tmul, h1, h2, swapH_tmul]
  · intro u v hu hv
    simp [map_add, hu, hv]
