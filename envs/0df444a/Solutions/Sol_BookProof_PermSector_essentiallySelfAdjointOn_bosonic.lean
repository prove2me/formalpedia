-- Prove2me | solution 1 for BookProof.PermSector.essentiallySelfAdjointOn_bosonic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-09T18:12:31.96376+00:00
-- url     : https://prove2.me/submissions/f6bd2eb1-6e71-4dfd-9778-b57fb3cdd353

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.essentiallySelfAdjointOn_bosonic
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_isReducingProjection_bosonicProj
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorDom
import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorDom
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
import Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn
      (redDom (bosonicProj Hs n) (sectorDom Hs D₂ n))
      (redOp (sectorOp Hs D₂ A n) (isReducingProjection_bosonicProj Hs n)
        ((permRep Hs n).commutes_avgProj
          (hD := permRep_mem_sectorDom Hs D₂ n)
          (permRep_commutes_sectorDom Hs D₂ A n))) := essentiallySelfAdjointOn_red _ _ hesa
