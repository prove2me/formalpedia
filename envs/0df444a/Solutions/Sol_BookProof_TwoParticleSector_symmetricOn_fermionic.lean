-- Prove2me | solution 1 for BookProof.TwoParticleSector.symmetricOn_fermionic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-24T06:49:20.953818+00:00
-- url     : https://prove2.me/submissions/6e127198-b2e6-40b7-923f-23e2db27ccab

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.symmetricOn_fermionic
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
import Theorems.Thm_BookProof_TwoParticleSector_sectorOp_swapH
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_fermionicProj
import Theorems.Thm_BookProof_ReducedEsa_asymProj_mem
import Theorems.Thm_BookProof_ReducedEsa_commutes_asymProj
import Theorems.Thm_BookProof_ReducedEsa_symmetricOn_redOp
import Theorems.Thm_BookProof_TensorCore_symmetricOn_sectorOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hA : SymmetricOn D₂ A) :
    @SymmetricOn ↥(sector (fermionicProj Hs)) _ _
      (redDom (fermionicProj Hs) (sectorDom Hs D₂ 2))
      (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_fermionicProj Hs)
        (commutes_asymProj (T := sectorOp Hs D₂ A 2)
          (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A))) := symmetricOn_redOp _ _ (symmetricOn_sectorOp Hs D₂ A hA 2)
