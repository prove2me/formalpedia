-- Prove2me | solution 1 for BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-09T22:22:47.579526+00:00
-- url     : https://prove2.me/submissions/19137af6-0079-49ce-963e-feda79df166f

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorCore
import Theorems.Thm_BookProof_TwoParticleSector_restrictOp_sectorOp_swapH
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_bosonicProj
import Theorems.Thm_BookProof_ReducedEsa_commutes_symProj
import Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
import Theorems.Thm_BookProof_ReducedEsa_symProj_mem
import Theorems.Thm_BookProof_TensorCore_essentiallySelfAdjointOn_sectorCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hcore : IsGraphCore D A)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) :
    EssentiallySelfAdjointOn (F := sector (bosonicProj Hs))
      (redDom (bosonicProj Hs) (sectorCore Hs D₂ D 2))
      (redOp (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2))
        (isReducingProjection_bosonicProj Hs)
        (commutes_symProj
          (T := restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2))
          (hUD := fun _ hx => swapH_mem_sectorCore Hs D₂ D hx)
          (restrictOp_sectorOp_swapH Hs D₂ A D))) :=
  essentiallySelfAdjointOn_red _ _
      (essentiallySelfAdjointOn_sectorCore Hs D₂ A D hcore 2 hesa)
