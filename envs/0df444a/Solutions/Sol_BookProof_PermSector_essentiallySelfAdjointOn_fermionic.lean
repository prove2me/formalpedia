-- Prove2me | solution 1 for BookProof.PermSector.essentiallySelfAdjointOn_fermionic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-09T18:14:22.611941+00:00
-- url     : https://prove2.me/submissions/2073bc2b-a4cf-4538-a1e1-ad3b321a499d

-- Generated from ChapterPermutationSectorEsa.lean — solution of BookProof.PermSector.essentiallySelfAdjointOn_fermionic
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_isReducingProjection_fermionicProj
import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorDom
import Theorems.Thm_BookProof_PermSector_signRep_commutes_sectorDom
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
import Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.PermSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn
      (redDom (fermionicProj Hs n) (sectorDom Hs D₂ n))
      (redOp (sectorOp Hs D₂ A n) (isReducingProjection_fermionicProj Hs n)
        ((signRep Hs n).commutes_avgProj
          (hD := signRep_mem_sectorDom Hs D₂ n)
          (signRep_commutes_sectorDom Hs D₂ A n))) := essentiallySelfAdjointOn_red _ _ hesa
