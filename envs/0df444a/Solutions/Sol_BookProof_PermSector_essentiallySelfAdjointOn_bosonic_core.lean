-- Prove2me | solution 1 for BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-09T18:14:35.98194+00:00
-- url     : https://prove2.me/submissions/5a66756c-7922-41ab-8e89-da2ec894d30c

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_isReducingProjection_bosonicProj
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorCore
import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorCore
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
import Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
import Theorems.Thm_BookProof_TensorCore_essentiallySelfAdjointOn_sectorCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hcore : IsGraphCore D A)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn
      (redDom (bosonicProj Hs n) (sectorCore Hs D₂ D n))
      (redOp (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n))
        (isReducingProjection_bosonicProj Hs n)
        ((permRep Hs n).commutes_avgProj
          (hD := permRep_mem_sectorCore Hs D₂ D n)
          (permRep_commutes_sectorCore Hs D₂ A D n))) :=
  essentiallySelfAdjointOn_red _ _
      (essentiallySelfAdjointOn_sectorCore Hs D₂ A D hcore n hesa)
