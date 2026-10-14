-- Prove2me | solution 1 for BookProof.TwoParticleSector.sectorOp_swapH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:20:51.093667+00:00
-- url     : https://prove2.me/submissions/aa47ad26-1880-4ba7-94f1-c4109e5d0de4

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.sectorOp_swapH
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_inclPow_swapDom
import Theorems.Thm_BookProof_TwoParticleSector_derPow_swapDom
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
import Theorems.Thm_BookProof_TensorCore_sectorOp_apply
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
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (x : sectorDom Hs D₂ 2) :
    sectorOp Hs D₂ A 2 ⟨swapH Hs (x : (Hs.pow 2).carrier),
        swapH_mem_sectorDom Hs D₂ x.2⟩
      = swapH Hs (sectorOp Hs D₂ A 2 x) := by

  obtain ⟨t, ht⟩ := x.2
  have hx : (x : (Hs.pow 2).carrier) = inclPow Hs D₂ 2 t := ht.symm
  have hsw : swapH Hs (x : (Hs.pow 2).carrier) = inclPow Hs D₂ 2 (swapDom Hs D₂ t) := by
    rw [inclPow_swapDom, hx]
  rw [sectorOp_apply Hs D₂ A 2 _ _ hsw, sectorOp_apply Hs D₂ A 2 x t hx,
    derPow_swapDom]
